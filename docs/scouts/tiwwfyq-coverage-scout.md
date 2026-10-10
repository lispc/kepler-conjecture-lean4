# GRUTOTI 测度覆盖链缺口地图（只读侦察，2026-10-10 归档）

> 盘面核实：PA23 恰 2 个 proof-sorry（4561 `p23_grutoti_cap_measure_cover`、
> 4623 `grutoti_pivot`）；GRUTOTI capstone（:4653）本体已是纯组装真证——
> 两笔 sorry 清零即整章闭合。

## 1. 十二件上游件逐一核实（当前盘面）

| 件 | 模块:行 | 状态 |
|---|---|---|
| TIWWFYQ | PA5:663 | 真证（每点落在某闭 Voronoi 胞） |
| TIWWFYQ_concl | PA2:5325 桩 / PackingConcl:550 | 桩 sorried；Concl 桥已由 PA5 真件 discharge |
| GLTVHUM_concl | PA2:3458 | 真证（2026-09-30） |
| GLTVHUM / GLTVHUM_lemma1 | PA6:1265 / PA6:1109 | 真证 |
| SLTSTLO1 | PA13:595 | 本体真证（吃上游传递债） |
| SLTSTLO2 | PA13:818 | sorry（Rogers 胞覆盖唯一性） |
| DUUNHOR_concl | PA2:3500 | 真证（PackingConcl:137 弱接口版仍 sorry） |
| RVFXZBU | PA10:197 | i=0,1,4 真证；i=2,3 sorry |
| RVFXZBU1/2/3_concl | PA2:4936-4954 + PackingConcl | 全 sorry 无 twin |
| DDZUPHJ | PA13:847 | sorry |
| QZKSYKG1/2 | PA14:895/932 | 双 sorry（2 是 ~1900 行 GIANT） |
| AJRIPQN | PA17:313 | sorry（该文件唯一 proof-sorry；PA18:1809 AJRIPQN_0 真证包装） |
| CONIC_CAP_INTER_CONVEX_HULL_4_GT_0 | PA15:2275 | **真证**——pivot docstring "PA15:828 still sorried" 是陈旧情报 |
| BARV_IMP_VORONOI_LIST_NOT_EMPTY | PA5:2240 | 真证 |

## 2. hcov 最短供给链（PA23:4551/4561）

```
LHS ≤ RHS：measure_mono（迹⊆D + 双方可测）        ← 已 banked 真证 [~10 行]
RHS ≤ LHS（逐点 z ∈ D）：
  ① D ⊆ ball u0 1 ∩ rconeGt u0 u1 c
     - r ≤ 1 球面零测差                            [~20 行]
     - D ⊆ rconeGt d ⊆ rconeGt c 需 c ≤ d          ← 缺口 G1
  ② ball1∩c-锥 ⊆ ⋃₀ rogers p23Fam = p23_C_sub_rogers(PA23:1958 真证) 实例 ← G1
  ③ z ∈ rogers vl0 → SLTSTLO1 → z ∈ mcell k V vl0, k≤4   [~30 行]
  ④ 排除 k=0,1（照抄 p23_cover_C 的 i=0/i=1 臂）    [~60 行]
  ⑤ X ∈ grutotiEdgeCells：mcellSet ✓ + B1 VX-前向桥 ← 纯组装（见下）
  ⑥ 双 mono 收口                                    [~20 行]
```

**缺口 G1（前提面，非数学）**：需 `hl/√2 ≤ d` + region 覆盖见证 `c`（`c ≤ d` +
`hcovW`）——冻结签名无这些关系；d < hl/√2 时恒等式很可能为假。GRUTOTI 调用点
（:4660-4662）手里全有（`p23_region_data` 一步导出），只是冻结私签名收不进来
——与 SF31 同流程。

**B1 VX-前向桥（新发现，纯组装非缺口，~60-100 行）**：
`X = mcell k V vl, k≥2, X≠∅, barV 3 vl, trunc1 vl=[u0,u1] ⇒ {u0,u1} ⊆ VX V X`，
组合 `HD_IN_MCELL`（PA15:257）+ `LEPJBDJ`/`LEPJBDJ_0`（PA11:472/500）+ ε-见证
分案（p.1=0 被 LEPJBDJ_0 杀；p.1=1 被 V∩X 单点含 u0 而 u1∈V∩X 杀；p.1≥2 后
LEPJBDJ@p 给 VX=V∩X ∋ u0,u1）。

**hcov 传递 sorry 债**（本体不新增）：SLTSTLO1 ← XNHPWAB1_concl(PA2:4821)、
OMEGA_LIST_N_IN_CONVEX_HULL(PA7:556)、XNHPWAB2(PA7:542)、MXI_EXISTS_concl
(PA2:4902) 均 sorry。**hcov 填证不需要 AJRIPQN**（从 p23Fam 正向构造，边标签
由构造自带）。

## 3. grutoti_pivot 同款地图（PA23:4615/4623）

前提 = `hr hr1 hd hd1 he hfin`（无 hs/hp/无 region 数据）。

```
逐点（p23_setSum_congr 收口，banked）：
  - nullSet 支：dihX=0 + vol(X∩D)=0                 [~20 行]
  - ¬nullSet 支：套 grutoti_cell_vol（:4063 真证）
      he 免费（grutotiEdgeCells 成员定义）
      hn : ¬nullSet(X∩D) ← k≥2 计数(p23_edge_cell_k_ge_two :628 真证)
          + 逐 k：k=3/4 走 CONIC_CAP_INTER_CONVEX_HULL_4_GT_0（PA15 已真），
          k=2 走 hw1 窄性 —— 全部需要 region 数据 ← 缺口 G1'
      hp/hw1/hw3/hw4 ← p23_region_data 逐字供给（同 G1，一个 SF 波）
  - 反向支（CAVEAT）：cellParams 描述为 [u1;u0,…] 的携边胞
      k=2：MCELL2_PERMUTE_01(PA14:822 真证)+affGe 对称 kit 镜像 [~100-150 行]
      k=3/4：真缺口 G3——dihX 定向 junk 语义 + S₃ 交换不变性
             （RVFXZBU i=3 类），照 HL §H(7441-7958) 案例分析重做 [~200-400 行]
```

pivot 不吃 AJRIPQN。与 hcov 共享：region 供给（同一个 SF 波）、grutoti_barV
链（下垫 PA15:578 HL_LE_SQRT2_IMP_BARV_1 **sorry**——整条 grutoti 链的传递债）、
setSum 组装件。

## 4. AJRIPQN 现状

`p23_grutoti_edge_pairwise_null`（PA23:4496 真证）就是"实例化即得"模板
（p23_mcell_reduce 归约 + 零测/正测度二分）。AJRIPQN docstring 的
Missing-pieces 已过时；真余债 = SLTSTLO2 + DDZUPHJ + RVFXZBU i=2,3 +
QZKSYKG1/2 + 960 行装配，**估 1500-3000 行，不在 hcov/pivot 临界路径上**。
警示：AJRIPQN 波会与 PA24 线抢 k′-识别同件。

## 5. 分级与推荐进攻顺序

| 级 | 件 | 估行数 |
|---|---|---|
| A（SF 前提波，待批） | G1+G1'：hcov 加 region 门、pivot 加 hs/hp/hu0/hu1/hne/hhl+hw1hw3hw4（同步 measure_facts 与 GRUTOTI 调用点） | 补丁 ~50-100 |
| A（一步装配） | B1 VX-前向桥 | ~60-100 |
| B（短装配） | hcov 填证 | ~150-250 |
| B（短装配） | pivot null 支 + u0-首向支 | ~100-200 |
| C（真缺口） | pivot 反向 k=2 镜像 ~100-150；k=3/4 反向 = 全场最硬 | ~200-400 |
| C（非临界可选） | AJRIPQN GIANT | ~1500-3000 |

推荐顺序：SF 前提波（A）→ B1 桥（A）→ hcov 填证（B）→ pivot B 支（B）→
pivot 反向 k=2 → pivot 反向 k=3/4（C）。**两笔债清零即 GRUTOTI 全章闭合。**

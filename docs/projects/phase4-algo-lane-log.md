# Phase 4 算法优化常驻车道 · 滚动日志（2026-10-12 设立，用户指令二）

> 使命：持续算法优化使求解 wall-clock 与 HOL 原版至少可比，消灭零收敛尾部
> （里程碑文档 §0 指令二 / §3 ①b）。全量重跑仍 deferred，样本级实验在本车道。

## W1（限额阵亡，遗产 /tmp/p4wave1 全部被 W1b 复用）
实验台建成：bb_arb.c/bb_arb_mono.c（C99 区间 B&B + 一阶 TM，FLINT/ARB）；
20 案 + BIXPCGW 4 split 案备弹；TADIAMB TM 证书 141MB（251,054 叶 101.2s 全闭）。

## W1b（2026-10-12）
**主攻战报**：split_0_2（BIXPCGW 7274157868_a 前半）**CLOSED**——裸区间
60,065 叶 54.8s；+TM+ite-hull2+gsplit2 → 49,869 叶 86.7s（−39%），TM invalid
26%→100%→**0**。证书 /tmp/p4wave1/bix7274s0_tm_cert.json（29.6MB，不入 git）。
**关键解剖**：50,487 叶 = disj 92.9% + TM 7.2%——域切分是使能器，闭合主体是
析取备选裸区间，TM 只管临界带。
**失败模式定档**：①TEWNSCJ（sqrt 族尾部）：ite-hull2 把 guard 跨 0 清零但对
sqrt/log 非正底 206,019（97.6%）无效，TM closed=0——**ite-hull2 对 ite 族
ω-complete、对 sqrt 族结构性无力**，尾部需 radicand 零等值面切分/换元（不同
武器）；②BIX 硬半 split_1_2 与 945 案（无 disj）未破，深度 TM 每节点成本是
主要矛盾。
**C→Lean 缺口（新发现）**：BIX 20 叶 TM 抽样 stage-A 重放 0/20——需真实
SqrtTMP/粒度证书进 TMParams（现 driver 用占位符；TADIAMB 多项式族零 sqrt 节点
所以绿）。修复方向已明，W2 工位。
**Lean 侧两 pilot 绿**：TADIAMB 20 叶（namespace 一行修复后）50.7s；
C4717061266 127 叶 110s（新造）。内核边际 0.8-2.2s/叶（ historic 21.4），
单叶固定开销 ≈9.3s（IExpr elaboration）。

**HOL 对表协议（三层）+ 首批数字**（口径锚 FormalVerifier.tex §Test Results，
i5-2.67GHz/2009；官方全章 5,000 核时/遍）：
| 层 | 口径 | 现状 |
|---|---|---|
| Tier 1 | 求解墙钟 vs HOL total 搜索份额 | **我方大幅占优**（4717061266: 0.02s vs 27.1s） |
| Tier 2 | 内核全重放 vs HOL formal_verification_time | 差 2-3 量级，但三杠杆实测：证书瘦身 438×（C471 vs 裸区间 55,668 叶）+ native_decide 6.1× + LExpr 去重 3-5×，叠加后**章节口径可与官方 5,000 核时同量级**（单案口径不达） |
| Tier 3 | 生产消费（银行/抽样/瘦身，叶数解耦） | 银行/银行抽样已绿 |

**TM vs BBTreeGD 决策材料（§0 用户点名，数字可直接引用）**：TM 在 ite 族已
ω-complete（guard 跨 0 清零）、在 sqrt 族结构性无力（TEWNSCJ 实证）；BBTreeGD
对比跑批建议以 TEWNSCJ/QZECFIC 为对照组。

**W2 建议**：①BIX stage-A 粒度收割修复（真实 SqrtTMP 进 TMParams）→ split_0_2
全证书落地（92.9% disj 叶走 emit_lean.py --bbg --disj-gd 现成路径）→ 求解层
68/176 → +0.5；②split_1_2/945 先 --tm-ddf 诊断；③sqrt 族尾部立项 radicand
零点预切分或 t=√u 换元发射器改造。
**遗产归档**：docs/assets/p4wave1/（两 pilot .lean + 测量 log 全套；证书不入 git）。


## W2 计算车道 · BBTreeGD 对照组 2×2 决策矩阵（2026-10-12，决策材料补齐）

协议：两臂同二进制 bb_arb 受控对照；4M 节点/1800s 双上限；并发 ≤2；CEX=0（全部零收敛未闭合，无反例）。

| | BB 裸档 | BB+TM 档 |
|---|---|---|
| TEWNSCJ | NOT CLOSED，4M 超限，11 未闭合叶，146s | NOT CLOSED，11 叶盒与裸档逐字节一致，145s；TM invalid 192 全为 sqrt/log 非正底（ite-hull2 已清 guard 跨 0） |
| QZECFIC_wt0 | NOT CLOSED，4M 超限，17 未闭合叶，1464s（366µs/节点） | NOT CLOSED，1800s 击杀；200k 探针：invalid 100,007（100% 非正底），但 valid=closed 100%——切掉负底半域即闭合 |

**裁决：sqrt 族 BBTreeGD 路线不成立**（4 格全灭：裸档叶数爆炸+TM 零改善且更贵）。**主武器 TM + sqrt 尾部立项第三武器**（radicand 零等值面预切分 / t=√u 换元）——QZECFIC 探针给出立项利好：负底半域切掉后剩余域 TM 有效即闭合。BBTreeGD 的多项式族快路径（4717061266 0.02s）不受影响。

**决策材料完成度：可以拍板**。证据双侧齐：TM ite 族 ω-complete（TADIAMB 251k 叶全闭 + split_0_2 49,869 叶）与 sqrt 族结构性无力（4 格全灭 + 非正底 100%）。
产物归档：docs/assets/p4w2/（矩阵 summary + 全部 run log）。未测残余：4M 外行为（预期 MKFKWU 级 ≥10⁹，不值得测）。

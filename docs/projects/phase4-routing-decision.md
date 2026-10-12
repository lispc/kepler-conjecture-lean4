# Phase 4 求解策略路由表 — 正式决策记录（2026-10-13，用户"按建议全部批准"）

> 决策材料：`docs/projects/phase4-algo-lane-log.md`（W1/W1b/W2 三波受控实验）+
> `docs/assets/p4w2/matrix_summary.txt`（2×2 对照矩阵）+ `docs/assets/p4wave1/`
> （测量 log 全套）。本文是 Phase 4 非线性不等式验证的**策略路由正式决策**，
> 消费者 = 强机器日 92 prep 重求解波 + 189 infeasible 波 + certified bank 尾部波。

## 0. 裁决

**放弃"TM vs BBTreeGD 二选一"的原问题形式，改为按表达式族路由的混合策略。**
每一行路由都有本周受控实验背书，无猜测成分。

## 1. 路由表

| 路由 | 表达式族 | 主武器 | 兜底 | 实证 |
|---|---|---|---|---|
| **R1** | 多项式/有理族 | **TM**（TADIAMB 类） | BB 析取 | TADIAMB 251,054 叶 100% 闭合 101.2s |
| **R2** | ite/guard 族 | **BB 域切分 + ite-hull2 + TM 临界带**（混合管线） | — | BIX split_0_2 CLOSED（49,869 叶 86.7s，TM invalid 26%→0） |
| **R3** | sqrt/log 族 | **第三武器**：radicand 零等值面预切分 / t=√u 换元发射器 → 切后区域交 TM | BB 单独**裁决出局**（2×2 全灭） | QZECFIC 探针：负底半域切掉后剩余域 TM 有效即闭合 |
| **R4** | 非严格/角点案 | **手证路线**（B V2 先例：角点零下确界手证四段完胜两求解器） | — | bank_GRKIBMPBV2_proof |
| 兜底 | 路由全失败残叶 | G4 数据波（HOL 同款"硬案重跑/人工"） | — | 549 lane 先例 |

## 2. 证据要点（详见 lane 日志 W1/W1b/W2 与对照矩阵）

- TM：多项式族碾压（251k 叶 100%@101.2s）；ite 族配 ite-hull2 ω-complete
  （invalid 26%→0）；sqrt/log 族结构性无力（TEWNSCJ closed=0，非正底 100%）。
- BBTreeGD：广覆盖骨干（BIX 92.9% 主体闭合）；sqrt 族 4 格全灭（4M 节点，
  裸档与 BB+TM 叶盒逐字节一致=加 TM 零改善）；多项式快路径 0.02s 不受影响。
- 混合管线形态已被 BIX 实证可表示（disj+TM 同证书），Lean 侧 CertTM 与
  BBTreeD 双内核均在树——**路由表不需要新 Lean 基建**。

## 3. 已批准的执行项（2026-10-13 用户"按建议全部批准"）

1. **第三武器 R&D 立项**：radicand 零等值面预切分 / t=√u 换元发射器改造——
   Phase 4 常驻车道 W4-W5（W3 的 formal_ineqs 考古先行对照 HOL 原方案）。
   验收锚 = TEWNSCJ/QZECFIC 对照组在第三武器下闭合。
2. **92 prep 族成分画像车道**（半天脚本）：812 记录按表达式节点类型
   （多项式/ite/sqrt 占比）分类——决定 R3 的核时预算与优先级。
3. **强机器日 runbook 引用本路由表**：灌装顺序按路由分批（R1 先行、R2 次之、
   R3 等第三武器+画像、R4 手证案已清）。

## 4. 局限与未测残余

- 两案 4M 节点外行为未测（预期 MKFKWU 级 ≥10⁹ 叶，无测量价值）。
- 92 prep 族成分未画像（执行项 2）。
- 编译/内核成本数字为 M3 Pro 单核口径，强机器需归一（Tier 2 三杠杆：
  瘦身 438× / native_decide 6.1× / LExpr 去重 3-5×）。

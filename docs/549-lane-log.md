# 549 加速项目 — opencode 车道日志

> 2026-09-22 启动。总体计划见 docs/549-acceleration.md（Kimi 交接）；本文件记录
> Phase 0 探针与后续里程碑的实测数据、方法注记与决策。

## Phase 0 探针（2026-09-22，当日完成）

### 探针 A：ite 普查 —— §4 风险撤销 ✅

全语料 176 案 `stats` 层统计（out/cases/*.json）：

- 总 ops 1,703,927，总 ite 4,361，**占比 0.26%**
- 36/176 案完全无 ite；最重案 SDCCMGA_* 也只 0.7%（12/1758）
- 5490182221 本身：ops 1067，ite 3，**0.28%**

结论：ite guard 跨 0 的逐支 TM 退化**不构成** 549/全语料关口。
TM2-C 的 ite 分裂工作不阻塞本项目主线。

### 探针 B：mono 定号率 + TM 可用率（549，600 叶均匀采样）✅✅

方法：`bb_arb.c` 新增 `--probe` 隐藏旗标（逐盒 TM 判定 + 带符号 df/σ dump，
σᵢ=Σⱼ wⱼ·ddfᵢⱼ 坐标线段 MVT；不二分不产证书）+ `probe_l1.py` 采样分析
（mmap 字节偏移采样，674MB 不整读）。样本 = 现 cert 叶均匀采样 n=600。

| 指标 | 实测 |
|---|---|
| TM valid | **600/600 (100%)**，invalid 原因分布为空 |
| TM 在叶原宽度直接闭合 | **600/600 (100%)** |
| mono（∃i: ∂ᵢf 区间定号） | **600/600 (100%)** |
| x₃ 单变量 | ∂x₃f **全部 600 叶严格 < 0** |
| 第二定号维（x₁/x₂/x₄/x₅ pos） | 各 ~170-205 叶（28-34%） |

解读：
1. **L2 强确认**：136 万叶全部能被 TM 在现有宽度闭合 → 现树纯碎裂自裸区间
   O(w) 精度需求；TM-first 重解的叶数削减应远超 10× 下界。
2. **L1 强确认**：549 表达式在 x₃ 上全局单调（该族不等式结构使然，与
   Flyspeck mono/convex 传统用法一致）→ 全树叶可降一维验证；
   30% 叶可降两维。
3. 方法注记（诚实口径）：采样基于**现存叶**（幸存者偏差）——树内更宽的
   祖先盒上 TM 失败率未测；自适应阈值（64 窗全灭减半）会吸收一部分。
   真实削减倍数以重解 pilot 为准（见下）。

### 探针 C：叶宽分布（同采样）

max 维 log2 宽度直方图：2⁻⁴ 占 74%（444/600）、2⁻⁵ 占 24%（144/600）、
其余零星。六维总和深度才是叶数来源（6 维组合爆炸），单维并不深。

### 零代码 L2 pilot（进行中）

bb_arb 的 bisection 循环已内置 TM-first + 自适应阈值（64 窗全灭减半/过半
加倍）。因此 **`bb_arb case.json --tm` 一条命令即 L2 pilot**：对比新旧叶数。

- 旧：1,354,264 叶（裸区间）
- 新：**1,331,880 叶（−1.7%，几乎零削减）**；TM att=2,663,747，
  **invalid 50%（1,331,842 次）全部 reason=2 guard 跨 0**；thresh 顶到 1.0
- 结论：**TM-first 单独对 549 无效（实测）**。探针 B 的 100% 原宽闭合为真，
  但树的深度由 guard 决策面决定：祖先盒上 TM 因 guard 跨 0 失效，
  TM 与裸区间卡在同一宽度——叶集 = guard 边界贴附细胞，两条路径同病。

## 549 结构解剖（guard 分析）

3 个嵌套 ite（= 分段定义，非 abs 语法糖）：

- cond 均为**判别式型多项式**（`−x₁²x₂² + x₀²x₃² + …`，~20-30 ops），
  非单变量符号测试；then/else 72-231 ops（含 atan/div 顶段）
- 根 ite 与两个内层 ite 的 cond 多项式高度相似 → 决策面或为同一/少数
  代数曲面
- **136 万叶 ≈ 贴附 guard 曲面的细胞数**：曲面分辨率的切向组合复杂度
  （探针 C：叶宽 2⁻⁴/2⁻⁵ max 维，六维总和深度不高、树是"宽"不是"深"）

## 战略修订（Phase 0 的真正产出）

| 杠杆 | 对 549 的实测/推断 | 处置 |
|---|---|---|
| L2 TM-first 单用 | **无效**（pilot 实测 0 削减） | 从 549 主线撤下；对非 guard 主导案仍有效 |
| L1 mono | 分支闭合侧有效（∂x₃f<0 全叶），但闭合不是瓶颈 | 降级为组合件 |
| L3 chop/精度 | 治精度不治 guard 有效性 | 与 M0 一起保持 Kimi 线 |
| **L2.5 guard 法向切分**（新提议） | guard 跨 0 时按 q 的敏感维切分而非最宽维；C 侧 only、内核零改动 | **下一实现目标** |
| **L4+L2 原始树种子**（假设升级） | 原始 Flyspeck cell 若天然对齐 guard 曲面（分段定义同源），则每 cell guard 立即可判定 + TM 直接闭合 → 549 塌缩到 ~23k cell 量级 | **下一探针（最便宜）**：拿 azure 549 cell 清单直接 `--probe` 测 TM 闭合率。注意 REPORT.md 教训：hminus 需按 choice 方程精确区间 |

风险注记：L4 对 BIXPCGW（y 空间）失败过，但那是"裸区间配原始树"；
549 是 guard 主导型 + 配 TM，机理不同——但必须先探针后重仓（本车道纪律）。

## 基础设施新增（本车道，已入 main 仓）

- `pipeline/interval/bb_arb.c`：`--probe FILE` 隐藏旗标（默认关闭，
  既有路径零改动；隐含 `--tm`）。输出 JSONL：f0/df（带符号 64 位外向
  舍入）/σ（mag）/closed/fail_reason。
- `pipeline/interval/probe_l1.py`：采样（`sample`）+ 分析（`analyze`）。

## M0 状态（闸门）

**未合入**：CertTM.lean 最后提交 = `30e84adf`（chopCeilTo 定义），evalTM
合成点接入无后续提交 → 按交接文档纪律，M2/M3 重仓前向 Kimi 要 150 叶
复测数字。M1 设计文档不依赖 M0，照常推进。

## L4 探针：azure 原始 cell 清单解剖（2026-09-22 续）

`reference/flyspeck/azure/ineqs.txt`（行格式 `NNN: NNN,(idv,cell): ineqm …`）：

- 23,237 cells 覆盖 **208 案**（需非线性验证器的 prep/terminal 子集）
- **83 案（40%）= 1 cell 闭合**（无切分树，纯全域）；重尾两案 6320/7318 cells
- **549 = `prep-5490182221` 单 cell**：x 空间 [#4.0,#6.3504]×6（= 我们的
  y 空间 [2,2.52]^6 逐点平方，域精确一致），body `dihatn_x + unit6*(−1.893)<0`
- 原始验证器单 cell 闭合的机制 = TM + 导数旗标 + convex + **abs/分段合成
  引理**（m_taylor_abs_pos_compose 类）——分段结构在求值器内部消化，
  不靠域切分

### 549 缺口的最终定位

| 层 | 原始 Flyspeck | 我们现状 |
|---|---|---|
| 域 | 1 cell 全域 | 136 万叶 |
| 分段结构 | 求值器内合成规则（abs/ite TM 规则） | TM_FAIL(2) bail → 裸区间 |
| 精度 | pp=4-6 + chop | N=2048 rung 阶梯 |
| 单叶成本 | ~75ms/cell（23k cells ≈ 0.48 核时反推） | 1.5s-28s |

**结论：guard 主导案例的命门 = taylor-model-design.md §6 故意跳过的
ite/abs hull 合并**。f 分段光滑（分支在判别式零点处 C¹ 吻合），
hull 合并的 soundness 路线：pointwise f(x) ∈ 两侧 TM 界的 hull；
df/df²/err 的安全合成（分量 hull / max / 与 C¹ 边界层论证）= M1/M2 的
核心设计内容，Lean 侧对应 CertTM 新增 ite-hull 内核规则（TMSafe 分支）。

### 修订后路线（549 车道）

1. **M1 设计文档扩容**：ite-hull 合成规则（C+Lean 双侧 soundness 论证）
   成为中枢；mono/convex 与 L2.5 guard 法向切分降为组合件
2. **决定性实验（C 侧 ~40 行）**：bb_arb TM 的 OP_ITE 改双支求值 + hull
   合成 → 全量重解 549 数叶数。若塌缩到 ≤100 叶量级 = 杠杆证实
3. M2：CertTM 加对应内核规则（含 soundness 证明），走 make check 纪律
4. L4 对 549 本身无树可导（1 cell），对 60% 有树案例仍是有用种子源

### ite-hull 决定性实验结果（2026-09-22 当日）

`bb_arb --ite-hull`（OP_ITE guard 跨 0 → 双支求值 + 保守常数 hull 合成，
soundness 注释在代码内；**仅驱动侧实验，内核侧 CertTM 规则归 M2**）：

| 指标 | TM-only | TM+ite-hull |
|---|---|---|
| 叶数 | 1,331,880 | **281,894（4.8×）** |
| guard 跨 0 invalid | 1,331,842 | **0** |
| 新 invalid 层 | — | div 越零 6,565 + sqrt/log 底非正 148 |
| 节点数 | 2,663,759 | 563,787 |

结论：
1. **分支合成机制证实**——guard 跨 0 清零，叶数 4.8×（且这是最保守的
   常数 hull；df-hull/保导数合成还有收紧空间）
2. 新阻塞层 = div/sqrt/log 的 TM 规则（6.7k 处）——**与 Kimi M0 刚落地的
   closed-trans 常数模型直接同源**，chop 接入后应再消一轮
3. 距原始 1-cell 还差：mono/convex 组合（L1 未叠加）+ 合成质量 + trans 层
   ——路径清晰，增量推进
4. ⚠️ 281,894 叶证书是驱动侧产物；内核验证需 M2（CertTM ite-hull 规则
   + soundness 证明）先行

## M2 + df-hull 波（2026-09-22 深夜，重启后重派工完成）

### M2：CertTM 内核 ite-hull 规则（`3e731659`，零公理零 sorry）

- 新增 `TaylorM.valueRange` / `iteHullTM` / `valid_iteHull` / `evalTMHull` /
  `evalTMHull_sound`；evalTM 语义未动（evalTMHull 对非 ite 构造子定义等价
  委托 evalTMH）
- ite 规则 = 双支求值 + 值域 hull + 常数合成，**guard 零依赖**（玩具自测：
  guard 含 div 越零时 evalTMH 仍 none、evalTMHull 照常 some 且模型相同）
- soundness 对 e 归纳，点wise 值语义 → 复合天然 sound；`#print axioms`
  全部 ⊆ 标准三公理
- 偏差注记：Lean err 界 |f(ρ)−f(y)| vs C 界 |f(ρ)−f0| ⇒ err_lean = 2·err_C
  （保守方向）；checkPosTMHull 接线建议已记录（emit_lean schema v3 下轮）

### C 侧 df-hull（--ite-hull2）：叶数定理级相同 + **发现常数版真隐患**

- df-hull 保留导数结构（df 分量 hull / ddf max / 基值并 err），四不变量
  (I1)-(I4) 全恢复；**常数版 df=ddf=0 破坏 I3/I4**——ite 之上再有 mul/div
  时 Df 低估、理论上可错闭合（549 实测未触发：df-hull 叶数与常数版完全
  一致 281,894，且 ΔW = ½Σ|Δdfᵢ|wᵢ = O(w²) → 0 有定理）
- **处置**：C 侧后续以 --ite-hull2 语义为准；Lean 侧因点wise值语义归纳、
  复合已 sound，无需返工
- **div越零 6,565 全定性**（Kimi 对接接口，tm_div_fail_diag 已注）：
  100% plain 型（与 hull 零关联）；失败点仅 2 个（ite7-then 支 ip=221
  与 ite7-else→ite0-then 支 ip=227 的 atn2 型商）；分母宽 log2 桶
  (2,6]:5719 → chop 压至 ~2³ 即可转定号——closed-trans/chop 直做，不碰 hull 层

### 三方叶数终表

| 版本 | 叶数 | guard跨0 | div越零 | sqrt/log |
|---|---|---|---|---|
| 裸基线 | 1,331,880 | 1,331,842 | — | — |
| 常数 hull | 281,894 | 0 | 6,565 | 148 |
| df-hull | 281,894 | 0 | 6,565 | 148 |

裸路径回归逐字节吻合（55668/111335）；make check 绿；已合 main。

### M2b + gsplit 波（`75eb7231`）

**M2b**：`checkPosTMHull(+sound)` / `evalTMHullFill`（逐节点镜像）落地；
emit_lean `--hull` 路径 + 修非 dyadic push_const 的 .div 节点饥饿缺口；
**真叶内核试点 20/20 求值成功、编译绿，但 0 PASS / 20 NEG**：

- 根因（组件级定位）：①C 侧闭合计 err=半宽，Lean 全宽 ⇒ 系统性肥一倍；
  ②嵌套 ite 每层 hull 宽 ×2 进 err（IT3 宽 25.7 → IT1 err 116）；
  ③区间积规则丢中心 AD 抵消（W 6.44 vs 真斜率小一个量级）→
  loBound −68…−374
- **诚实口径：C 侧 4.8× 尚不能直接转成可验证证书**——schema v3 三件套
  （evalTMHullD guard 定号单支 / df-hull 合成 / 斜率保真）从"优化"升级为
  "实证必需"，评审清单已交 Kimi

**gsplit（TM 梯度 |Df|·w 引导切分）：负结果归档**——+10.9% 更差
（312,578）。机理：贪心切 guard 曲面法向饿死切向细化，贴附细胞铺得更开；
叶数下界在切向分辨率。M3 维持最宽维；div 6,565 确认与切分层无关
（TM-invalid 节点走 fallback），归 chop/closed-trans。

### schema v3 第一刀：evalTMHullD（0/20 → 16/20 PASS）

- guard 裸区间定号 → 单支求值（零 hull 宽），跨 0 退双支；关键修复：
  catch-all 委托 evalTMH 使嵌套 ite guard-sqrt 必败（上轮 0/20 的真实失败
  模式）——改全构造子自递归 + soundness 全归纳重证；axioms 标准三
- **同证书同 20 叶复测：16 PASS**（全部 guard 定号单支，loBound
  +0.36…+0.65，上轮 −1.7e2…−2.1e7）；4 straddle 叶仍 NEG（−3.4…−6.2）
- **C 侧 --hull-stats 交叉验证吻合**：全量 281,894 叶 = single 75.34% /
  straddle 24.66%（恰 1 次 hull、嵌套深度全 0——×2 err 在证书叶结构性
  不存在）；20 叶逐盒 16/4 与 Lean PASS/FAIL 完全一致
- 结论：**549 现有 80% 证书叶内核可验证**；剩余 20%（69,538 straddle 叶）
  差 df-hull 合成 + err 半宽语义——最后一公里的路径完全明确

## 下一步（三更）

1. **df-hull Lean 合成**（最后一刀）：∃-slope 语义下 C¹ 拼接余项界；
   err 半宽对齐（Lean |f(ρ)−f(y)| 语义的覆盖估算按 C 半宽折算）→ 翻转
   4 NEG → 全量 281,894 叶发射 + stage-A
2. div/sqrt 6.7k chop/closed-trans 消解（Kimi 线，接口已备）
3. 与 Kimi 同步：16/20 交叉验证 + schema 评审清单 + div 接口
4. L4 种子树对 60% 有树案例复用（排后）

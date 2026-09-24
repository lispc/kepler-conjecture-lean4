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

### gsplit2 负结果 + 200 叶发射演练（`a0ac7af7`）

**gsplit2（guard 引导切分）：决定性负结果**——281,120 叶（straddle −0.34%）。
机制：straddle 叶 TM 首次尝试即闭合（付 1 次 hull 宽 loBound 即 >0），
从不进二分决策；且贴附细胞盒真跨 guard 曲面 ⇒ 任何 sound 区间求值永跨 0
——**"劈到定号"数学上不可能，df-hull Lean 合成 + err 半宽对齐被实证为
唯一路径**。双回归逐字节吻合。

**200 叶全量发射演练**（emit_hull_pilot.py + C549Hull200.lean）：

- **158/200 PASS**：single 150/150 全过；straddle 8/50 免 df-hull 翻正
  （同象限子群，16%）→ 可验证叶上修 **~79%（~223k）**
- 通量：内核 decide **21.4 s/叶**、4× 完美线性、RSS 40GB/50叶封顶并发
- 全量外推：**~1,675 core·h**（裸基线 10,800 的 6.5×）；12-25 并发
  墙钟 2.3-5.8 天；CPU 未吃满、内存封顶
- 管线缺口单（→Kimi）：stage-A hull 全量化 / shard ≤20-50 叶 /
  PASS-only 发射 / mode 进 manifest / 汇总定理 ∧ 写法固化
- 首建失败回退记录：汇总定理 ∷= shard 名类型错已修

### df-hull 合成（iteHullTM2）+ native_decide 提速（`c8ad6870`）

**df-hull：合成层做到语义最优**——锚点判定：Valid 锚真值 f(y) ⇒ 跳变项
必需且由双支 fB 区间距离给出（比 C 链更紧）；交叉案 witness 取选中支自身
斜率 ∈ hull（零宽度项）；**无连续性前提，对任意 ite 跳变 sound**。
试点：single 16/16 零回退；straddle loBound 收紧 **10⁴⁶**
（根 err 2^74.1 → 2^1.3）——**剩余发丝 NEG 已逐级仪器化定位到分支自身
余项**（ε_e=2.23，纯 atan/div 链 T3 支，与合成层无关；C 侧闭这 4 叶靠
存储锚点半宽语义 premium≈ε_e/2——语义性差距）。**翻正路径 = div/sqrt
分支余项压薄（ε_e 2.23 → <1.1，Kimi closed-trans/chop 线的精确靶子）**。

**decide 提速**：native_decide **6.1×**（21.4 → ~3.5 s/叶；全量
1,675 → **275 core·h**）。公理形态与 DECISIONS.md 2026-09-19 逐字同形
（每定理一条 scoped axiom），但 `Kepler.Interval.Cases.*` 不在现行例外
范围——**投产需新 DECISIONS 条目 + 人工批准**（推荐一次 native 关 50 叶
合取 = 1 axiom/shard，证据已捕获）。AST 重复率 **574%**（去重需 CertTM
let 节点，再 3-5×）。rung 超配 16×（8 仍 PASS）——stage-A 自适应最小
rung 的余量诊断信息。M5（≤10 core·h）需砍求值体积 1-2 个量级：
去重 + 证书瘦身 + 求值架构出 Lean 运行时。

### 549 车道阶段总结（相对原版 Flyspeck 的位置）

- 叶数：1,331,880 → 281,894（4.7×）；内核可验证 79%（~223k）+
  straddle 层合成已最优，余项层是最后 ~20% 的靶子
- 核时：10,800 → 275（native_decide 后，6.5×→39× 累计 vs 基线）；
  vs 原版 0.48：~570×（从 22,500× 起步）
- 剩余差距全在：①div/sqrt 分支余项（Kimi 线）②求值体积（去重/瘦身）
  ③叶数折叠（mono/convex L1 未上）

### 余项压薄（--tm-tight）+ 证书表去重 MVP（`7d1ca613`）

**余项压薄**：解剖定位——根余项 100% 在 T3 atan/div 支，肥在 atan Mg''
全局帽（真 sup 0.6495 vs 码内 1）；Schwarz 候选形 = sound no-op（否证链
归档）。atan sup 收紧后：4 straddle 叶 ε_e −38~−41% 全 CLOSED；
**549 全量 281,894 → 212,798 叶（−24.5%）**。lane log 的 ε_e=2.23 系
证书口径，C 侧活体 0.45-0.73——<1.1 靶子 C 侧已独立解决有余。
Lean 翻正预估：err 消费宽度 k=1.5 → 4/4；k=2 → 3/4（Leaf5 刀刃叶）。
双回归逐字节吻合。

**证书表去重 MVP**：`LExpr n k` 方案落地（否决 letD：IExpr 在 Expr.lean
+11 求值器爆炸半径）——旧求值器一行未动，全链 soundness + axioms 干净。
**诚实口径：折叠加速仅 1.1-1.4×**（证书免费子树非成本大头）；成本在
证书消耗链（10^90 级 fB 上 atan 链，折叠需重产 params）——
`tmHullLeafProbeL` 已就位，下一轮 stage-A-let 才能吃到真收益。

### 阶段位置（vs 原版 0.48 核时）

tight 后全量叶数 212,798；native_decide ~3.5s/叶 → **~207 core·h**
（基线 10,800 的 **52×**；原版的 ~430×）。剩余三杠杆：
①div/sqrt 残余 6,713（chop/closed-trans，Kimi 线）②证书消耗链去重
（stage-A-let）③mono/convex 叶数折叠（L1）。

### stage-A-let 负结果 + facePos 落地（`94d89947`）

**stage-A-let：去重杠杆正式关闭**——全折叠 0.97×（±8% 噪声）。decide 成本
∝AST 体积前提被证伪：折叠链仅占内核求值 ~1%；成本由唯一 atan/div/sqrt
链 + 内核固定开销主导（与 native_decide 6× 互证）。全折叠净负（探针层
+3.1s/叶 = +183 core·h）。**架构建议**：折叠方案移植 bb_arb（C 原生
entries-first 队列 ~ms/叶），Lean 探针降级抽查——恢复单层成本。
50 叶批量探针 44/6 与 speed 模块逐叶吻合；mantissa 队列 19.7 叶/分钟。

**facePos（M1 核心数学）落地**——`C549Mono.lean`（718 行）+ `emit_diff.py`：
- facePosLo/Hi（线段 MVT：`exists_hasDerivAt_eq_slope`）+ 
  derivIExpr_hasDerivWithinAt（DerivSafeOn 归纳链式法则，ite 定号分支）+
  checkPosFaceLo/Hi(+sound) 双叶组合——零新公理，CertTM 零改动
  （语义层全部放试点模块，爆炸半径最小化）
- 试点 5/5 判定一致；折叠方向按 stage-A 实测定向（lo 面）
- **诚实口径**：折叠对 2.4× 单叶成本（导数叶 2184 节点 34s）→ 净吞吐
  **3.2×**（非理论 7.7×）；导数叶的 574% 重复可走 LExpr 再压
- 叶数折叠预期：212,798 → ~2.8 万叶（7.7×）
- 边界：DerivSafeOn 证明项未发射（hD 显式前提，per-div/sqrt 定号证书
  叶 + iteNeg 链待做）；ite-else 支待做；迷你端到端已完整放行

### 阶段位置（七更）

tight 212,798 叶 + native_decide ~3.5s/叶 = **~207 core·h**；
facePos 全量后 ~2.8 万叶 × 2.4× 折叠对成本 → decide 口径 ~70-90 core·h，
native 口径 ~10-15 core·h——**M5（≤10）进入射程**。剩余三杠杆：
①facePos 全量化（DerivSafeOn 发射 + ite-else）②div/sqrt 残余 6,713
（Kimi 线）③native_decide 扩围（待批准）。

### facePos 全量化第一波 + T5（`make check` 绿，已合 main）

**facePos 全链闭环**（C549Mono +393/−90 + emit_mono.py + C549Mono2）：
- derivIExprM 双模式（iteNeg/iteNN）——ite-else 支补齐，链式法则一次证明
  覆盖双模式
- DerivSafeOn 证书发射：每叶 3 张 TM 证书叶（guardNeg 224 节点/div 分母
  151/sqrt 底 150）+ 2 内联常数分母；discharge 引理族逐节点拼装
- **全链 fold 定理达成**：面叶 + 导数叶 + 证书叶 decides ⇒
  `0 < e.evalReal ρ`（全盒语义正性，非 Bool 一致性）——3/3 试点全绿，
  axioms 标准三
- 边界：else 支真叶试点（该 3 叶实测定号负）/guard 触 0 零测叶诚实 NEG/
  abs-guard 拒发/lnK 无实例

**T5（Kepler 主线）**：Assembly `contraveningFan` 真化（经 ContraFan，
TameLp 同型接线）——§2c 占位 **11→10**，Assembly sorry 13→12，sorryAx
仅沿双核流动，审计行永久入 §5。

### facePos 全量评估 + 导数叶去重/右移（`8e61e2ca`）

**全量评估（212,798 叶精确普查 + 221 叶全链实测）**：
- 资格：guard 定号 then **77.6%**/straddle 22.4%；**else 支结构性空集**
  （双 guard 多项式逐字节相同——mode=false 机制保留但 549 无实例）
- facePos 可回收 C 侧 guard 包络保守性 **10.4pp（~22,000 叶）**
- 全链 PASS **50.7%**：瓶颈 cert 层（guard 证书叶损 35.3%）；face 零损失；
  方向 100% lo；112 条 Sem 定理 axioms 全标准三
- 发射坑修复：simp only 折叠定理 35min/叶不收敛 → have/show/rw 零开销
- **净收益表**：mono+÷7.7 粗化 = 233 decide/**67 native core·h**
  （wall 2.6h@25 并发）；无粗化净负；保本线 ≥3.7 叶/折叠组

**导数叶去重（负结果）+ 真杠杆（rung 右移）**：
- 成本归因：闭环 arctan(1) rung-2048 **值宽传播 59%**（去重不可及）；
  多项式段 ≈0；去重 1.02-1.04×（与 stage-A-let 同型，机理闭环）
- **rung 2048→128：导数叶 38.6→16.5s、面叶 32.5→10.6s**，全 PASS 且
  loBound 逐位不变（充分性由逐叶 stage-A 探针把守）→ 折叠对
  2.19×→**0.83×（低于基线）**⇒ facePos 净吞吐 **3.2×→~9.2×**
- 建议：emit 层钉死 rung=128 + 逐叶 PASS 自适应（薄余量叶回退 512）

### 阶段位置（十更）

组合口径（mono 折叠 + ÷7.7 粗化 + rung-128 折叠对 0.83× + native）：
外推 **~30-50 native core·h**（wall <1h@25 并发）——**M5（≤10）只差
最后 3-5×**，剩余来源：cert 层瘦身（guard 证书叶 35.3% 损耗）、
div/sqrt 残余 6,713（Kimi 线）、native_decide 扩围（待批准）。

## 下一步（十一更）

1. cert 层瘦身：guard 证书叶为什么损 35.3%——逐叶归因 + 收紧
   （与 tight 传播口径对齐？）
2. rung-128 右移正式化（emit 层 + 自适应回退）+ mono 折叠全量预演
   （≥1000 叶批量）
3. div/sqrt 6,713（Kimi 线）；native_decide 扩围（待批准）
4. Kimi 同步包全量更新

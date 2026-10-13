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

## W3（2026-10-12/13，前任限额阵亡于 00:25，续作接管 /tmp/p4w3/）

**主工位 1：rung/gran 阶梯实验（split_0_2 首个 tm 叶）——全轴扫尽，判定负结果 + 根因钉死。**
- 阶梯矩阵（leaf 0 lb，负=未证 pos；真值 mpmath 40 位核=+0.0306，角点 [0.0257, 0.0356]，ite 极性按内核 CertTM.lean:2781 guard<0→then 校正）：
  (128,−80,−80)=−6.30（W2 v2 逐字节复现）/ (2048,−80,−80)=−6.22 / (128,−80,−96)=−6.30 / (2048,−112,−112)=−6.17。
  **rung×gran×out 三轴全部 ≈ −6.3，阶梯不可能翻转**；W2 commit 的"margin −4e-406 近失"在全部 4 配置均不复现（疑为对探针行 (m,e) 的误读），本波勘误。
- **根因（精确有理区间算术，mpmath 交叉核）**：叶盒上 3/54 个 ite guard 真跨 0（guard 27/48/51，其 sqrt radicand 有零等值面穿过盒内）→ 内核 `evalTMHullD2` 对 straddle ite 付双支 hull 宽 ≈6.3 ≫ 真值 0.03。这是**证书结构缺口，非精度缺口**：C 侧闭叶靠 `--gsplit2`（guard 引导切分，bb_arb_mono.c:2355"让 straddle 叶变成 guard 定号单支叶——Lean 内核只能验证定号单支叶"）+ thresh 0.03125，gsplit 子盒不进证书 → 镜面重放结构性不可能 PASS。
- **修复路线已量化**：guard 引导二分（每步选 guard 跨宽最大下降维）在深度 ≤12 内把 leaf 0 拆成 13 个子盒、12 个定号、1 个残差——**每坏叶 ~10-30 子盒量级，W4 可行**。实施侧二选一：(a) Lean 侧 stage-A 对 NEG 叶做镜像 gsplit + 子盒 params，stage-B 发射 BBTreeGD 分裂节点（推荐，零 solver 重跑）；(b) C 侧把 gsplit 子盒写进证书（动 bb_arb + 重解）。第三武器（radicand 预切/换元）与本路线互补：预切消灭 radicand-straddle 于发生前。
- W1b log 复核：split_0_2 的 TM invalid 100% = guard 跨0（25,310/25,310），sqrt 非正底=0——与 TEWNSCJ/QZECFIC（100% 非正底）是**两种不同的失败模式**，第三武器设计要分开对症。

**工位 2：disj 主体解耦——kernel 消费端到端首次全绿。**
- 前任遗产：disj stage-A pilot 7/7 PASS（rung 12, −64）已绿（FillParams 判定侧）。
- 本波补齐 stage-B：`--bbg --disj-gd` 发射 7 叶 BBTreeGD（Base+Shard1），**lake build 绿，顶层定理 `_pos`（∃ g ∈ goals, g.eval ρ）公理 = 标准三**（propext/Classical.choice/Quot.sound）。
- 落库修复：emit_lean.py `base_file_bbgd` 缺 `set_option maxHeartbeats 0 / maxRecDepth 1000000`（7 叶 Base 的主 prog Expr elaboration 即超 200k 心跳，W3 实测）——+6 行。
- 放量口径实测：7 叶 Shard decide 4.17s（≈0.6 s/叶，disj:0 支小表达式 rung 12）；Base 一次性 elaboration 687s（46k 叶可摊）；46,861 disj 叶 stage-A（data 模式 runMainDisj，记忆化后 ~1 s/叶）≈13 CPU 时 + stage-B decide ≈8 CPU 时——1-2 晚机时，W4 可放。
- 坑：LEAN_PATH + `/tmp` 模块 `lake env lean -o` 有 root-directory 限制——pilot 走 untracked scratch 模块 + `lake build`（用完即删）；`lake env printenv LEAN_PATH` + 真实 lean 二进制 + CWD=模块根 是 /tmp 三件套可行解。

**工位 3：stage-B decide 成本实测（定 3,626 叶批量方案）。**
- TM hull 侧（checkPosTMHull，1,190 sqrt certs 填满，rung 128）：1 叶 decide+elaboration 122.7s，公理 [propext, Quot.sound]，**decide ≈ 1-2 分/叶** → 3,626 叶 ≈ 90-120 CPU 时，×10 shard ≈ 10 晚时。批量的真正瓶颈不是 stage-A（~4.5 CPU 时）而是 kernel decide——W4 立项"decide 成本工程"（shard 粒度/并行/rung 降档）。
- 注意 kernel 警告：`exponent 496 exceeds threshold 256`（Dyadic 幂未被求值）出现在 decide 内——decide 仍收牌（公理干净），但 W4 应加 `set_option exponentiation.threshold` 显式化。

**工位 4：formal_ineqs sqrt 机制考古（对照清单，喂第三武器立项）。**
- 原方案三板斧：①atn/asn/acs 全域固定多项式 enclosure（informal_atn.hl：半角迭代 t↦t/(1+√(1+t²)) 四次把 arg 压到 [0,0.1] + 交替级数 21 档固定系数表，零参数零 rung 零失败模式；asn=atn(x/√(1−x²)) 带域检查，acs=π/2−asn）；②sqrt 两层同一条硬规则（informal_interval.hl:103 与 formal arith_float.hl:4130 都是 radicand lo≥0 否则 failwith——**无 straddle 处理**，搜索层 fail→subdivide，代价一次符号检查）；③monotonicity 降维（m_verifier.hl:1099 m_mono_pass_gen：per-cell 偏单调 ∂ⱼf 定号→只验极值面；convex glue ml/mr；raw_intervals_flag；adaptive_precision；certificate.hl Result_pass_ref 引用压缩）。
- 关键结构差：**formal_ineqs 表达式语言没有 ite**——分支在 bank 归一化层拆成独立不等式，verifier 从不面对 guard-straddle；Taylor 层 atn 值界=固定表（informal_taylor.hl:505），与ours trans .arctanK 同构但无 rung/certs。
- 对照结论：①我方 radicand 预切=把 HOL 的"便宜 fail→subdivide"升级为"预切零等值面"（必要，因我方 TM 尝试贵 2-3 量级）；②guard-straddle 应在第零层消灭（prep 层 guard 提升=HOL 忠实路线）或镜像 gsplit（本波主工位路线）；③monotonicity 降维是我方全缺的免费武器；④atn 固定表启示：窄 arg 可零参数化省 rung。

## W3 收尾附记（2026-10-13 午后，编排者代收——车道 agent 已于晨间限额阵亡，diagSB 系孤儿进程）

**diagSB（13 子盒解释跑）事件账**：agent 阵亡后 `lake env lean --run diagSB.lean`
（PPID 已变 launchd=1）继续独烧一核 3h+，stdout 块缓冲（13 行输出凑不满 4KB）
零落盘——无法分辨进度。用户令"杀掉重编译跑"，12:03 杀。

**"重编译跑"复核结论（编排者实测 + CertTM 源码锚）**：
1. **直接 kernel decide 探针 = 结构性不可能**：`tmHullLeafProbe` 走
   `evalTMHullFill2`/`evalIParamsFill` 镜像，sqrt mantissa 用 `sqrtMantissa`
   现算，内含 `Nat.sqrt`——CertTM :4187-4199 docstring 明写 "Compiled runs
   only (`Nat.sqrt` does not kernel-reduce)"。实测：13 盒 13 定理
   `…map (·.1) = some true := by decide` 全数 "reduction got stuck at the
   Decidable instance"（/tmp/p4w3/diagSB13_build.log；scratch 用完即删）。
   这不是 bug 是设计：探针=证书**发现**层，内核=证书**消费**层。
2. **原生 exe 路 = 死**：lean_exe 会连带 Mathlib 全量原生编译（天级）。
3. **正规重跑路线 = `emit_lean.py --hull` 两段式**（:1045-1064 有完整说明）：
   stage-A 逐盒探针发现证书三元组（解释跑，估 ~10-30 分/盒，与被杀的 3h/13
   盒相容——缓冲假象下可能已近尾声）；stage-B bake 进 `TMParams.sqrtCerts`
   后 `checkPosTMHull = true/false := by decide`（122.7 s/叶已实测）——NEG
   叶也收（`= false`，证的是 compiled-run/kernel AGREEMENT）。13 盒全程
   ≈ 4-8 小时，**W4 体量，且与镜像 gsplit 修复路线实施本就是同一件事**
   （stage-B 发射器现成，缺的只是子盒→stage-A 的批量驱动）。
4. **实验不阻塞任何结论**：C 侧预测已在——diagC0.out（09:21）给出 sb0
   精确侧 loBound ≈ −1.5·10^302 × 2^−1742 ≈ −10⁻²²² < 0（NEG），与车道日志
   "12 定号 + 1 残差"的残差盒位置吻合（sb0 = 分区最顶片，guard 零等值面穿过）。
   Lean 侧对拍属 W4 修复路线的验收环节，随实施一并做。

**W3 落地件清单**：①本日志（四工位+本附记）；②`pipeline/interval/emit_lean.py`
`base_file_bbgd` 补 `maxHeartbeats 0 / maxRecDepth 1000000`（+6 行，7 叶 Base
主 prog Expr elaboration 即超 200k 心跳——W3 实测，disj stage-B 发射的必要修）；
③scratch 探针与 13 子盒实验产物全在 /tmp/p4w3/（易失，结论已抄录于上）。

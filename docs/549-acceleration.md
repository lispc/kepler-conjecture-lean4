# 549 加速项目交接(opencode 车道)

> 2026-09-22,Kimi 整理。目标:把 5490182221 的内核验证成本从现状 **~10,800 核时**
> (136 万叶 × ~28s/叶,墙钟 ~19 天 @24 并发)压到原始 Flyspeck 同量级
> (**1,726 秒 ≈ 0.48 核时**,见 `reference/flyspeck/formal_ineqs/docs/FormalVerifier.tex` 实测)。
> 差距 ~22,000×,分解:叶数 ~2,700×(主)、单叶成本 ~6×(副)。

## 0. 车道纪律(先读)

- 你在主仓 `/home/scroll/repos/kepler-conjecture-lean4`(分支 wip/auto-packing 或 main)工作。
- **绝对不要动** `/home/scroll/repos/kepler-g4e/`(Kimi 工作树)下的任何文件和进程;
  机器上在跑的 runner(549 构建、BIXPCGW repair、257 stage-a、LP 重跑)都归那边,
  不要 kill/重启任何你不拥有的进程。
- Lean 构建用限流 wrapper:`export PATH=/home/scroll/toolchains/g4cap/bin:$HOME/.elan/bin:$PATH`,
  `export ELAN_NO_OVERRIDE_NOTICE=1`。重活 `nice -19`,并发 ≤8。
- 主仓的 `pipeline/interval/out/` 下有 4.4GB 证书数据,bb_arb 直接可用。

## 1. 已有基础设施(全部已合入 main,直接用)

**Taylor 模型双侧(TM0-TM2 已验收,零 sorry,公理仅标准三)**:

- Lean 侧:`lean/Kepler/Interval/CertTM.lean`(~1200 行)——`TaylorM`/`Valid`/`evalTM`/
  `evalTMH`(hybrid fallback)/`checkPosTM(H)`;支持 +−×÷√、atan/ln/sin;`TMSafe` 谓词;
  ite/abs 自动退 fallback。`CertG.lean` 有 `taylorLeaf` 构造器,`bb_soundG` 签名不变。
  **注意**:`Dyadic.chopCeilTo`(30e84adf)已进 main,但它在 evalTM 合成点的**完整接入
  是 Kimi 侧在制工作**(agent-31 跑 150 叶复测),接入完成后会再合 main——开工前
  先确认 main 上 CertTM 是否已有 chop 接入的后续 commit,没有就等或先问。
- C 侧:`pipeline/interval/bb_arb.c` 的 `--tm` 路径——`tm1_t` 前向 AD,TM 先行判定 +
  盒宽自适应阈值,证书叶带 `tm` advisory 块(schema v3 雏形)。单测 `test_tm_unit.py`,
  基准 `bench_tm.sh`。裸路径零变动(逐字节回归过)。
- 设计文档:`pipeline/interval/taylor-model-design.md`(383 行,含 §5 风险清单);
  进度/踩坑笔记:tm0/tm1/tm2/tmc-progress.md(同目录)。
- 探针机制:`pipeline/interval/tm1_probe_gen.py` 生成 `Cases/Repair/TM*Probe*.d`
  驱动,可统计任意失败叶样本的 TM 通过率(TM1 实测 0/150 → 定位到 trans 段;
  TM2 待 chop 复测)。

**调研数据**(成本模型的依据):

- 原始 Flyspeck:23,237 个预切分 cell,官方 ~5000 核时/遍,`reference/flyspeck/azure/results/`
  日志实测 ~9,275 核时,审计跑两遍。降维技巧(mono/convex)是其证书 node 类型的核心。
- 我方实测:已发射 15 案 668 万叶;单叶成本双峰(普通算术叶 ≲1.5s,rung-12 高阶叶 28s);
  539 全体裸区间基线 ~21.5 CPU 年(下界)。详细数据在 Kimi 的调研报告,要问。

## 2. 四个杠杆(按预期倍数排序)

**L1 单调性/凸性降维(主杠杆,预期 10-1000× 叶数削减,目前完全没做)**
- 原理:cell 上 ∂ⱼf 定号 → f 下界在端面取得,验证 n−1 维面即可(Flyspeck Result_mono);
  ∂²ⱼⱼf 定号 → 只查两个端面(convex glue)。
- 几乎免费:evalTM 每叶本就算出 dfB(一阶导界)和 ddf(Hessian 界),定号检测=读符号位。
- 新增:证书节点 faceLeaf/convexSplit(双侧)+ soundness(坐标向 MVT,难度低于已完成的
  trans 规则)。参照 `reference/flyspeck/text_formalization/verifier/certificate.hl:10-28`
  的 result_tree 类型和 `m_verifier_main.hl:30-50` 的选项(allow_derivatives/convex_flag)。

**L2 TM 判定进 stage-A/repair 驱动(TM3,预期 10-100× 于边界带)**
- bb_arb --tm 已有;还需要:emit_lean schema v3(tm advisory 进证书)、stage-A 驱动 TM-first、
  内核 checkPosTM 量产适配。549 的 136 万叶绝大部分是裸区间 O(w) 碎裂。

**L3 chop + 精度下放(单叶 28s → 目标 <2s)**
- chopCeilTo 杀 mantissa 爆炸;TM 时代 Hessian 只需数量级精度,trans rung 可从 N=2048
  大幅下放(原始方案 pp=4-6,约 9-14 位十进制)。

**L4 导入原始切分树做种子(2-10×,可选)**
- 原始非中点切点贴在真实 margin 脊线;`reference/flyspeck/azure/` 有 549 的完整 cell 清单。
  注意:agent-29 实验证明"导入树+裸区间"不行(9/9 FAIL),必须配 TM/降维才有意义;
  hminus 常数需按 choice 方程求精确区间(pipeline/interval/out/orig_tree/REPORT.md 末节)。

## 3. 里程碑与验收

| # | 内容 | 验收 |
|---|---|---|
| M0 | ~~chop 接入 evalTM + 150 叶复测~~ **已完成 2026-09-22**(`97f5e6ce`) | chop 生效(200s→3.2s/叶);复测 **0/150**——根因=sqrt(radicand≈0) 处一阶模型数学上不可能 + ite/abs hull;**"单叶 ≥95%"口径作废,TM 价值改按二分树总叶数口径测量(M4 成为真正的验收点)** |
| M1 | mono/convex 双侧设计文档 | Kimi/用户评审 |
| M2 | Lean:faceLeaf/convexSplit + soundness + pilot | 内核闭合,公理干净 |
| M3 | C:bb_arb mono/convex 检测 + 证书发射 | 单测 + 裸路径回归 |
| M4 | **549 重新求解 pilot**(新驱动全量跑) | **叶数 < 1 万**(现 136 万) |
| M5 | 新证书内核验证计时 | **总成本 ≤ 10 核时** |
| M6 | 回归零变动 + 合 main + 更新 STATUS | make check |

M2/M3 可并行。先确认 M0 数字再重仓 M2/M3。

## 4. 边界与风险

- ite guard 跨 0 的逐支 TM 是 prep 家族的关口(TM2-C 实测 split_1_2 残余 100% 来自 ite);
  549 若 ite 占比低则不阻塞本项目——先查 549 表达式的 ite 节点数。
- 旧 549 构建(6321 分片)仍在 g4e 跑,作对照组;新证书出来后再决定去留。
- evalFill/evalTM 双侧镜像是已知事故多发点(见 taylor-model-design.md §5.1):
  改判定逻辑必须双侧同步,或让 C 侧读 Lean 生成的判定表。

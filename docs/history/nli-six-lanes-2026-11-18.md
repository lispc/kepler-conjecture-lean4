# nli 六车道战役总结 — 2026-11-18

> **性质**：历史总结，记录当天六条 sub-agent 车道的结论、实测加速、失败边界与下一步。
> 实时状态、在飞与排队以 `docs/priority-queue.md` 为准；逐件数学细节以
> `docs/nli-campaign.md` §1.10–§1.13 为准。本文不替代账本。

## 0. 一句话结论

**精巧数学确实能省掉大量计算，但不存在一个可以不加区分接管全部 nli 的通用引擎。**
代数化、联合包络和共享证书有效；通用超越 Bernstein、整盒凹性归约和当前 Lean
数据表示分别被实测否证或阻塞。当天没有实际减少 SORRIED，也没有落库新 Lean 文件。

- 基线 AQ @`e4c384e6`（2026-11-18）：SORRIED **51 = 50 `nli*` + 1 hLP**，Text 0；
  AXIOM 585 不变。
- 六条车道全部收线，无遗留后台车道。
- 三份 Lean 资产经编排者从快照独立编译与公理检查，但**未落库、未提交**。

## 1. 六车道交付与判词

| 车道 | 判词 | 核心结论 |
|---|---|---|
| `g4-hessian-scout-w1` | 有条件 GO | dihXf 全部 36 个二阶偏导有 atan-free 闭式；后续发现 lmfun 权重 factor-2 错误，修正后正反结论仍成立，旧数值作废 |
| `b0-joint-envelope-w1` | 数值 GO | 八债拆成六债共享与两条 η 曲线；五主债由三张支撑面覆盖，96 角点塌缩为 60 对称轨道 |
| `bernstein-representative-w1` | 多项式 GO；通用超越 NO-GO | ZTG 多项式义务根盒 1 叶；√/atan 整盒界误差和组合规模爆炸 |
| `fhb-seam-curve-w1` | UNRESOLVED | η126 二次边界、显式根式曲线和三个归约接口真证；FHBa 尚缺 m3/m4/m5 与 3-D guard 正性 |
| `g4-hessian-lean-w1` | UNRESOLVED | W5 与全部 6 条对角二阶导真证；整盒逐坐标凹性归约被精确反例证伪 |
| `bernstein-kernel-pilot-w1` | UNRESOLVED，止损 | 81 系数小叶未通过；MvPolynomial/Finsupp/Quot 的 Decidable 表示成为结构性阻塞，完整定标不存在 |

详细入口：

- Bernstein：`nli-campaign.md` §1.10；快照 `~/c17_backup/lane_snapshots/bernstein-representative-w1/`。
- B0 包络：§1.11；快照 `~/c17_backup/lane_snapshots/b0-joint-envelope-w1/`。
- Hessian 与 factor-2 勘误：§1.12；快照 `g4-hessian-scout-w1/`、`g4-hessian-lean-w1/`。
- FHB η 曲线：§1.13；快照 `~/c17_backup/lane_snapshots/fhb-seam-curve-w1/`。
- Bernstein Lean 止损：快照 `bernstein-kernel-pilot-w1/ORCHESTRATOR_NOTE.md`。

## 2. 已独立验收的 Lean 资产

| 文件 | 内容 | 编排者验收 |
|---|---|---|
| `FhbEtaCurve.lean`（405 行） | η² 商式、二次边界、判别式、显式根式、盒内/边界性质、三个归约接口 | RC=0，约 9 秒、5.8 GB；11 个公理面标准三；岛协议消费探针通过 |
| `Gamma4ConcaveBridge.lean` | W5 `concaveOn_of_hasDerivAt2_nonpos` | RC=0，约 2.2 秒、2.2 GB；标准三 |
| `Gamma4DerivSecond.lean` | 6 条对角 `dihXf_hasDerivAt2_x{i}_x{i}` 与 `g4s_quad_deriv` | RC=0，约 5.1 秒、5.8 GB；8 个检查公理面标准三；消费探针通过 |

这些文件是可复用资产，不是债务闭合。各快照的 `ORCHESTRATOR_CHECK/` 保存独立验收日志。

## 3. 加速效果与证据等级

### 3.1 已测量的结构改进

**ZTG 多项式义务（Python 侧）**：

- 原 bespoke：32 角点 + 32 条 line 证书 + 31 步 Jensen 链；
- Bernstein：根盒一张六维张量、1 叶；
- q=64/25：1,215 系数、57,142 B、约 0.42 秒；
- q=36/25：81 系数、2,488 B；
- rad2/eta 守卫：1–3 叶、毫秒级。

这是明确的多项式证书结构优势，但 **Python GO 不等于 Lean pilot GO**；当前主要价值是
未来重构和复用，不能直接折算成根面减债或 Lean 核时加速。

### 3.2 有依据但尚未兑现的潜力

- B0 的六债可共享求值、支撑面和候选点；不再天然需要六套独立分析。
- atan-free 二阶导把切片凹性变成纯多项式符号问题，可用一维精确证书。
- FHBa 已从完整未知收缩成两组明确义务：地板单调性与 3-D guard 正性。

**B0 的整盒闭合成本目前不可估。** 原“96 角点 + 少量符号义务即可闭合”的设想
已被整盒凹性反例推翻，不能继续引用为加速预算。

### 3.3 明确的负结果

- 通用超越 Bernstein：BIX 代表节点 √ 整盒误差为 slack 的 2,662 倍，
  `chord(S)^5` 达 126,607,131 系数；不做“整盒有理界 + 单分数组合”。
- 整盒逐坐标凹性：`∂²Q/∂y2²` 的 4×4 精确网格有 4 个正值；原角点归约不可用。
- 当前 Bernstein Lean 表示：设计 A 的 `DecidableEq` 不可归约；设计 B' 的通用核
  虽曾单次 RC=0，但当前 WIP 仍有 exponent/Finsupp 错误和 heartbeat 超时。
  81 系数叶未通过，1,215 根叶未开始，**完整 wall/RSS/olean/axioms 定标不存在**。

## 4. 推荐下一步

### 第一组：完成 FHBa（目标 −1）

1. `fhb-floor-mono-w1`：证 m3/m4/m5，即 ∂γ4/∂y3、∂y4、∂y5 在 B0 上为正，
   复用 Gamma4Deriv 链并直接喂 `fhb_hba_of_floor3`。
2. `fhb-g3pos-w1`：处理 N3D、7 个边界片和最终一维曲线
   `γ4(y1,y2*(y1),2⁴) ≥ 7e−3`。304 个 Newton 种子只作侦察，不当证明。

两条可以独立工作，但都必须成功才能装配 FHBa。FHBv2a 在 FHBa 真闭合前不动。

### 第二组：独立直接减债

`cell3-wt-math-w1`：先 wt2A 后 wt1，利用 y5/y6 严格单调性归约为 y4 一维证书，
接管 `math5-w4` WIP，目标各 −1。它不与 FHB 共用前置，适合并行。

### 保持搁置或低优先

- B0 母定理：原整盒凹性方案停止；需要新的分段/代数证书，不重试旧三路。
- 完整 BernsteinKit：未获合格 81 系数叶，不量产。
- `bernstein-kernel-representation-w1`：仅低优先 fresh 候选，显式指数向量、81 叶、
  两小时止损，用户另批。
- D `lp-dual-representation-audit-w1`、E `terminal11-family-compression-w1`：
  保留为零 Lean 候选。
- S2b 量产、通用超越后端、农场、certtm/TM3/Mono*/D 层：继续 hold。

## 5. 经验教训

1. **先代数化，再做证书。** ZTG 的成功来自结构，超越函数直通后端则失败。
2. **联合处理优于逐债优化。** 共享包络、共享原子和共享求值比单条不等式技巧更有杠杆。
3. **Lean 最小闭环必须尽早做。** Python 的低叶数、低 ρ 和小数据不能证明 kernel
   的 Decidable 表示可用。
4. **采样不是证明，单次 RC=0 也不是最终交付。** 必须核当前 WIP、0 error、公理面和
   实际消费接口。
5. **自研脚本自洽不等于定义正确。** Scout 的 factor-2 错误在首次复跑中未暴露，
   后续独立有限差分才抓住；标定必须回到定义和独立算法。
6. **角点归约先找反例。** `max(g,c−η²)` 和整盒 Q 都说明局部凹性不能随意外推。
7. **通知与锁都以事实为准。** completed/timed_out 后先查 wire、快照和进程；
   stale lock 只在无人持有时清理，反复 resume 不等于进展。
8. **“数据而非代码”仍需数学与表示设计。** 不合适的指数/Finsupp 表示本身就能让
   kernel 失败，数据化不是自动降本。
9. **止损保存产出。** 即使 UNRESOLVED，也应留下可复用 Lean 件、精确负结果和下一步
   最小义务，而不是继续烧轮次。

## 6. 总结

当天最重要的正面结果是：**多项式 Bernstein、atan-free 二阶导和 B0 联合包络都证明了
数学压缩确实存在。** 最重要的负面结果是：它们各自都有明确适用边界，不能合成一个
未经验证的通用自动工厂。下一轮应优先完成 FHBa 与 cell3 这类已有明确解析路径的债，
而不是再开新的通用引擎。

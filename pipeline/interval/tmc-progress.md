# TMC 进度笔记（bb_arb 一阶多元 Taylor 模型前向 AD，设计 §2 的 C 侧半）

> 运行记录。每个可验证子步骤一段：做了什么 / 验证命令与结果 / 下一步。
> 工作树 `/home/scroll/repos/kepler-g4e`（分支 wip/g4-emit）。纪律：nice 19、
> 测试并发 ≤2、内存 <10G、长测试 setsid + 状态文件、输出在
> `pipeline/interval/out/tm_c/`。

## 0. 任务与已读（2026-09-21）

任务：`bb_arb` 加 tm1_t 一阶多元 TM 前向 AD（设计文档 §1.3/§2.2/§2.3），
驱动 TM 先行、失败退裸区间；验收 = 单元级 O(w²) 过估 + 实战级
prep-BIXPCGW_7274157868_a_split_0_2.json 对照。

已读：`taylor-model-design.md` 全文、`bb_arb.c`（1274 行原版）、
`lean/Kepler/Interval/CertTM.lean`（TM0 evalTM 语义基准：TaylorM=
y/w/fB/dfB/err，loBound = fB.lo + Σ(dfᵢ·[loᵢ−yᵢ,hiᵢ−yᵢ]).lo − err）。
FLINT 3.3.1 头文件核对了全部用到的 mag/arf/arb API
（mag 算术外向上取整、arf_set_mag 精确表示 mag 名义上界、
arb_get_lbound_arf/arb_get_ubound_arf 端点界）。

## 1. 实现（bb_arb.c，+约 500 行）

- `tm1_t`（§2.2 草图落地）：f0 中心球 / df[n] 偏导球 / ddf[n²] 盒上 |∂²| 幅值
  界（mag_t，粗精度）/ err（mag）/ W（振幅界缓存）/ valid 标志。
- `eval_prog_tm`：单遍 RPN 前向 AD。一阶项在中心点 y（盒中点，精确 fmpq
  经 arb_set_fmpq 入球）做球算术（积/商法则、链式解析导数）；ddf 用粗精度
  （--tm-hprec，默认 32）区间算术按积法则/链法则传播：
  mul 的 Hᵢⱼ ≤ Hf·Bg + Bf·Hg + DfᵢDgⱼ + DfⱼDgᵢ，div 的商法则二阶展开，
  一元 g∘f 的 H ≤ Mg''·DfᵢDfⱼ + Mg'·Hf（sqrt/log 的 Mg 用盒值域下界 c；
  atan Mg''=min(1,2Bf)；sin/cos 用 |sin t|≤min(|t|,1)）。
- err = ½·Σᵢⱼ wᵢwⱼ·ddfᵢⱼ **全序对和**（T-D0，不用 Schwarz），每节点从其
  自身 ddf 重算；W = Σ|dfᵢ|wᵢ + err。
- 判定：y 是中点 → 线性项逐维端点正好 ±wᵢ → loBound = f0.lo − W。
  loBound > 0（arf 外向算术）→ 叶闭合，cert hit="tm"。

**语义一致性说明（与 CertTM.lean 的关系）**：fB/df/err 字段语义与 Lean
`TaylorM.Valid` 完全一致（∃-斜率形式的合法 TM），但 err 数值路线不同——
Lean TM0 走纯代数合成余项（无 Hessian），C 侧走 Hessian 盒界（设计 T-D0
原文）。两者都是 sound 上界；C 侧只是 advisory（内核重算），不构成冲突。

**两处超出任务书字面的动态处理（记录偏差）**：任务书说 "ite/abs → valid=0
退裸区间"。但验收案例 prog 含 54 个 ite + 18 个 abs，严格照做则 TM 在实战
案例**永远不可用**，验收 (b) 失去意义。实现改为运行时判定（仍 sound）：
- ite：guard 在盒球上裸区间可判定（复用 eval_prog 严格模式）→ 盒上 f 恒
  等于一支，递归 TM 该支；跨 0 → 本叶 TM 不可用。hull 合并不做（§6 保持）。
- abs：盒值域定号 → identity/neg（Flyspeck m_taylor_abs_pos_compose 的定号
  特款）；跨 0 → 不可用。
两者都是"盒上退化为单个光滑分支"的情形，不违反设计 §5.2 的 C² 前提。

**驱动整合（§2.3）**：`--tm` 开启（**默认关闭**，裸区间路径零变动——已验证
原版/新版输出逐字节一致，见 §2）。每叶 TM 先行（盒宽 ≤ 自适应阈值时），
失败/不可用退既有裸区间+阶梯+disj+二分。阈值窗口自适应（64 次尝试一窗：
全灭减半、过半且 <1 加倍，初值 --tm-w0=0.25）——只影响性能不影响
soundness。新 CLI：`--tm --tm-prec(256) --tm-hprec(32) --tm-w0 --tm-debug`。
证书叶 hit 串新增 "tm" 值（schema 不变）。

**GCC 告警备注**：eval_prog_tm 在 -O2 下触发 -Wstringop-overflow/overread
误报（FLINT 数组 typedef arb_t=arb_struct[1] 的对象尺寸分析幻觉；-O1/-O3
均 0 告警，20 行最小复现也无），用 `#pragma GCC diagnostic` 局部屏蔽并
注释说明。原版基线 0 告警，新版除该屏蔽区外 0 告警。

## 2. 验证：裸路径回归（已过）

```
gcc -O2 -std=c99 -Wall -Wextra bb_arb.c（零告警）
test_case_ite.json / test_case_ite_cex.json / test_case_x2minus2.json：
  原版（HEAD 编译）vs 新版（不带 --tm）stdout/exit code 逐字节一致。
```

## 3. 验收 (a)：单元级（已过）

`test_tm_unit.py`（新建）：解析导数已知的小函数，TM 界 vs 真实值域。

```
f1 = x²+√(y+1)−3（mul/sqrt/add/sub）  过估比 3.99, 4.00   （O(w²)）
f2 = atan(xy)+x/(y+2)−sin(y)（atan/div/sin）  过估比 4.06, 4.03
f3 = x−sin x（一阶项中心为 0，余项主导）  过估比 8.00, 8.00（O(w³) 档）
f4 = x²+√(y+1)−1 > 0：驱动级根叶一步 TM 闭合，cert hit="tm"
```

全部包住真实值域（loBound ≤ 真 min、hiBound ≥ 真 max），过估量严格
O(w²)（盒宽减半 → 过估 ÷4）。案例 JSON 与 cert 在 `out/tm_c/tm_unit_*`。

## 4. 验收 (b)：实战级 prep-BIXPCGW split_0_2（进行中）

案例：7 元，prog 总长 ~20.6k 指令（54 ite / 18 abs / 1625 sqrt / 241 atan /
276 div），disj 1 条。裸区间基线（任务书口径）：600s/4M 节点超时。

**诊断（实测，仪器：TM_FAIL 原因码 + invalid 直方图）**：

- 前 20k 节点 TM 尝试 788 次全部 invalid，主因 **ite guard 跨 0**
  （785/788），少数 sqrt 底非正（3/788）。
- 20k 节点时裸/TM 两侧都只剩 **7 个未闭叶**（爆炸核心），这些叶是
  宽约 1.3–2.7 的**粗盒**（x2..x6 区间大重叠）。
- 代表叶（leaf 0）上 sqrt 底数子式：裸区间估计 [−715, 1519]，TM 估计
  f0=295.4、W=419 → loBound=−123.6 也跨 0——该盒尺度下 sqrt 域条件
  （底数盒值域严格正）不满足，TM 不可用是**真实的**（W 由真偏导驱动，
  非过估伪影；需更小的盒让 Hessian/线性项缩下去）。
- 结论：TM 何时开始有用 = 盒小到 sqrt 底数脱零 + guard 可判定之后；
  是否比裸二分更快到达闭合 = 本次对照实验要量的东西。

**对照实验结果（split_0_2，修复后二进制，bench_tm.sh 顺序跑，日志
`out/tm_c/bench_*.log`）**：

| 配置 | nodes | leaves | TM closed | wall |
|---|---|---|---|---|
| bare | 120129 | 60065（全 disj） | — | 67.7s |
| TM（w0=0.25） | **100973** | **50487** | 3626（att=10240, valid=8334=81%） | 111.0s |
| TM（w0=1.0） | 100973 | 50487 | 3626（同，阈值不敏感） | 114.7s |

- 节点/叶数 **−16%**；墙钟 +64%（该案例 prog 达 20.6k 指令，TM 单遍 ≈
  (1+n+n²)≈57 个量 vs 裸 1 个，叶均成本天然高——C 侧墙钟不是目标指标，
  下游内核 decide 按叶数计费，叶数才是）。
- 全案例闭合均靠 disj:0 或 tm；主 prog 裸判定 0 叶闭合（ite guard 所致）。
- 历史口径记录：`out/bbarb_results3.txt` 里**未分割**的
  BIXPCGW_7274157868_a 曾 rc=0 leaves=70870 nodes=141739 闭合；
  任务书"600s/4M 超时"疑为更早管线状态/别的 split。如实记录：当前树上
  split_0_2 裸区间 120129 节点可闭合，TM 把它降到 100973。
- **split_1_2 才是超时级案例**（任务书"600s/4M 超时"口径对应它；本机更慢）：

| 配置 | nodes | 结果 | TM 统计 | wall | 峰值 RSS |
|---|---|---|---|---|---|
| bare | 4M（上限 rc=2） | 未闭叶 **25** | — | 72.4min | 743MB |
| TM | 4M（上限 rc=2） | 未闭叶 **47** | att=1475136, valid=718143(49%), **closed=718054（valid 即闭合 100%）** | 160min | 776MB |
| bare @20 万节点 | 200000 | 未闭叶 13 | — | ~4min | — |
| TM @20 万节点 | 200000 | 未闭叶 **7** | att=13008, valid=3066, closed=3066（100%） | ~6min | — |

- TM 侧 4M 上限时残余叶反而多（47 vs 25）：节点预算相同时 TM 把预算花在
  临界带的直接闭合上（71.8 万叶由 TM 闭合），前沿快照不可直接比较；
  20 万节点同预算对照（7 vs 13）更能说明 TM 推进更快。**但结论要诚实：
  TM 没有在 4M 节点内挽救 s1**——它把光滑盒上的叶子成批直接闭合，
  残余爆炸核心仍在 ite guard 边界上。
- invalid 原因直方图（两个 split 全部）：**100% 是 ite guard 跨 0**
  （s1: 756993/756993；s0: 1906/1906）。div 越零 / abs 跨 0 /
  sqrt-log 底非正均为 0——sqrt 域条件（§4 诊断的 reason=5）只在
  浅层粗盒出现，深层全是 guard 边界。这精确印证设计 §5.2 的已知限制：
  TM 要求盒上 C²，piecewise 边界叶不在 TM 射程内。设计"明确不做"的
  ite 支级合并若要救 s1，需要的是**逐支 TM 分别判正**（两支 loBound
  都 >0 则叶闭合，pointwise 语义下 sound，无需 hull）——留给后续
  （Lean 侧需对应的 taylorLeaf-ite 证书形式，agent-31 的 TM2 trans
  规则之外的新构造）。

**接力状态**：bench 全部跑完（`out/tm_c/bench.status` ALL-DONE）。
无遗留运行中进程。下一步：commit。

**修复记录（复审发现）**：一元链法则的 Df（内层偏导盒上界）原先在 df 被
新值覆盖**之后**才取，低估 ddf → err 偏小（soundness 漏洞，单测碰巧仍过）。
已改为 switch 前先取 Df，重跑单测全过（过估量略增、比值不变 ≈4.00/8.00）。
修复后 split_0_2 数字即上表（修复前二进制曾得 94989 节点/TM closed 2229，
作废）。

**接力状态（旧，已结清）**：~~bench_tm.sh 还剩 bare_s1 / tm_s1~~ 全部完成，
数字见上表。~~若 resume 时 bench 还在跑……~~（已 ALL-DONE）。

**另完成的可选项**：证书 tm advisory 块（§2.3）已实现——TM 闭合叶携带
`"tm": {"rung_c":..,"rung_h":..,"err_exp":..}`（center 默认中点省略）。
单测 f4 证书已验证输出形状。仅 --tm 路径产生该块，既有证书消费者不受影响。

**中途回归**：全部编辑后裸路径三案例（x2minus2/ite/ite_cex）stdout、
退出码、证书 JSON 与 HEAD 原版逐字节一致。

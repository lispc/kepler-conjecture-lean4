# 主定理 e2e 可达性地图（v2，树指标）

> **v2（2026-11-03）**：验收口径改为「树优先」（DECISIONS 2026-11-03「树越大越好」）：
> 主指标 = **K-REACH / COVERAGE / SHIMS / ORPHANS**；`K-SORRIED` 为信息项（不设单调目标）；
> `K-AXIOM` 为护栏。旧版地图（下方「归档：v1」起的 §0–§4）保留作审计，
> 其中「可达 Kepler 声明 218,326」等读数用的是已废弃计数，不可与 v2 的 K-REACH 直接比较。
>
> **树只认 proof-term 可达，不认 import 闭包。** 地图是静态常量依赖遍历：从根出发，
> 只展开 `ConstantInfo.value? true`（theorem/opaque 的值），子节点只收
> `Kepler.*` / `_private.Kepler.*`。`import` 进来但不在任何根证明项里的声明**不计入**
> K-REACH——它们正是 ORPHANS。

## v2.0 指标定义

| 指标 | 定义 | 用途 |
|---|---|---|
| **K_REACH** | 根 proof-term 闭包内 distinct Kepler 声明数（树节点；含 axiom/opaque） | 主指标：树越大越好 |
| **K_SORRIED** | 根闭包内**值里直接含** `sorryAx` 的声明数 | 信息项，不设单调目标 |
| **K_AXIOM** | 根闭包内 Kepler 公理数（含 `native_decide` 的 `*_native_decide.ax_*`） | 护栏：不得增长 |
| **K_MODULES** | K_REACH 声明所在的不同模块数 | 树广度 |
| **K_UNIVERSE** | 当前 env（= `import` 闭包）内 `Kepler.*` / `_private.Kepler.*` 声明总数 | COVERAGE 分母 |
| **COVERAGE** | K_REACH / K_UNIVERSE | 树覆盖率 |
| **TOTAL**（legacy） | **有值**的可达声明数（旧 `TOTAL_REACHABLE_KEPLER_DECLS`） | 仅历史对照 |
| **ORPHANS** | K_UNIVERSE − K_REACH（import 闭包有、树里没有） | 主指标之一 |
| **SHIMS** | 树内 `Kepler.Text.*_concl` 且存在同名 `*_concl_discharged` / `*_discharged` | 主指标之一 |

> **COVERAGE 分母口径**：`K_UNIVERSE` = 当前 `env.constants` 中根分量为 `Kepler` 或
> `_private.Kepler` 的全部声明（即本脚本 `import` 闭包载入的 Kepler 声明总数），不是整个
> Mathlib/全局宇宙。e2e 脚本的 import 闭包 = `Kepler.Assembly` 的传递 import。

### 旧 `TOTAL_REACHABLE_KEPLER_DECLS` 的口径 bug（2026-11-03 记录）

1. **名字与定义不符**：它只统计 `ConstantInfo.value? true` 有值的节点，因此**漏掉**
   axiom/opaque 等无值声明。HEAD `5384f11d` 实测差 702 = 624 条可达公理 + 78 条其它无值声明。
2. **历史文档混用两种计数**：2026-10-26 文档写「可达 Kepler 声明 218,326」，而 TSV 的
   `TOTAL_REACHABLE_KEPLER_DECLS` 是 2,077,226（约 10×），两个数不是同一个仪器产物；
   v2 起只保留一个定义（K_REACH），旧名不再使用（仅输出兼容行）。
3. **工单所说「total 把 Mathlib 也算进去」在本 HEAD 仪器上不可复现**：遍历栈只收
   `isKeplerName` 子节点，且 `TOTAL 2,077,393 < K_UNIVERSE 2,093,836`，远小于任何含
   Mathlib 的量级。真实缺陷是命名误导 + 「只算有值节点」，不是 Mathlib 泄漏。

## v2.1 当前基线（仪器校准后）

### 基线 A：HEAD `5384f11d`（c1 Stage 1 之前）

| 指标 | 值 |
|---|---:|
| K_REACH | **2,078,095** |
| K_SORRIED | **123** |
| K_AXIOM | 624 |
| K_MODULES | 4,168 |
| K_UNIVERSE | 2,093,836 |
| COVERAGE | 99.25%（2,078,095 / 2,093,836） |
| TOTAL (legacy) | 2,077,393 |
| ORPHANS | 15,741 |

- `SORRIED` 的 123 行源清单与 [`docs/e2e-reachability-map.tsv`](e2e-reachability-map.tsv)
  **逐行一致**（`comm -3` 无输出）：仪器校准通过。
- `K_SORRIED` 与 v1 的 `SORRIED` 定义相同，因此数值可直接衔接。

### 基线 B：c1 Stage 1 `a31177c9`（PackingConcl 进 e2e）

| 指标 | 值 |
|---|---:|
| K_REACH | 2,078,302 |
| K_SORRIED | **129** |
| K_AXIOM | 624 |
| K_MODULES | 4,171 |
| K_UNIVERSE | 2,094,054 |
| COVERAGE | 99.25%（2,078,302 / 2,094,054） |
| TOTAL (legacy) | 2,077,600 |
| ORPHANS | 15,752 |

**129 是真实债显形，不是回归**：c1 新增 `PACKING_CHAPTER_MAIN_CONCLUSION_discharged`、
把假 `RDWKARC_concl_discharged`（`:= RDWKARC`，而 PA19 `RDWKARC` 是 sorry）改为真 donor
`rdwkarcConcl_pc`，Assembly 加一行 rewire；e2e 根由此进入 packing chapter。旧假债
`PackingAuto2.UPFZBZM_concl` 出列（−1），PA15×5 / PA16 `QZYZMJC` / PA2 `GRUTOTI1_concl`
七个真源显形（+7），净 +6。`K_AXIOM` 624 不变。

### 基线 C：批 1 收官 `a522078c`（PA15 五源闭合 + terminal11-T0 陈述物化）

| 指标 | 值 |
|---|---:|
| K_REACH | **2,078,505**（较基线 B **+203**） |
| K_SORRIED | **123**（−6 = PA15×5 + LA1 terminal 黑盒撤源） |
| K_AXIOM | 624 |
| K_MODULES | 4,171 |
| K_UNIVERSE | 2,094,279 |
| COVERAGE | 99.25%（2,078,505 / 2,094,279） |
| TOTAL (legacy) | 2,077,803 |

- **PA15**（`f8b3e46f`）：`SUM_PAIR_2_SET` / `MCELL_SUBSET_BALL_4` / `PACKING_BALL_BOUNDARY` /
  `BOUNDS_VGEN_klemma` / `CARD_MCELL_CONTAINS_POINT_klemma` 五源全闭，公理面标准三；
  另闭 bonus `BOUNDARY_VOLUME`（非源）。
- **terminal11-T0**（`a522078c`）：`main_nonlinear_terminal_v11` 从 `def … := sorry`（任意
  Prop，贡献 1 个 sorry 源节点）物化为 109 条具名 `mainEstimate_*` 陈述 + 词表/访问器
  （零证明风险）；黑盒源出列，树 +~200 条陈述节点，109 条子债在树里可数、可派工。
  证书 glue（T1）未做，`Kepler.Assembly.nliMainNonlinearTerminalV11` 仍是 sorry 源。
- 剩余 123 源构成（本基线实测）：Assembly 77 / **PA25 30** / LA32/33/20 各 3 /
  PA16 `QZYZMJC` 1 / PA2 `GRUTOTI1_concl` 1 / LocalConcl 1 / 其余 LA 单条若干。
  在飞批 2 直接瞄准其中 QZYZMJC 与 GRUTOTI1_concl。

### 基线 D：批 2 首笔落库 `ed6b5a1e`（PA25 B0 replay）

| 指标 | 值 |
|---|---:|
| K_REACH | **2,078,646**（较基线 C +141） |
| K_SORRIED | **112**（−11 = PA25 B0 的 11 直源） |
| K_AXIOM | 624 |
| K_UNIVERSE | 2,094,306 |
| COVERAGE | 99.25%（2,078,646 / 2,094,306） |

- PA25 `real_model_*` 直源 30 → 19；poolc-w4/w5/w6 的 11 条重放件 + 5 条 kit 件全标准三
  （验证车道 `pa25-b0-replay` 判决 GO，编排者过闸）。批 2 另两条（PA16 `QZYZMJC` /
  PA2 `GRUTOTI1_concl`）在飞，落库后预计 112 → 110。

### 基线 E：S1 接线波 + QZYZMJC 闭合（`ebe0d0b7` + `2dea72f0`）

| 指标 | 值 |
|---|---:|
| K_REACH | **2,079,707**（较基线 D **+1,061**） |
| K_SORRIED | **135**（wiring 显形 +24 真实债；QZYZMJC 闭合 −1） |
| K_AXIOM | **624（护栏不动）** |
| K_MODULES | 4,179（+8，树广度） |
| K_UNIVERSE | 2,094,333 |
| COVERAGE | 99.29%（2,079,707 / 2,094,333） |

- **S1 `localconcl-wiring-w1`**（`ebe0d0b7`）：LocalConcl 新增聚合 capstone
  `localconcl_wire_capstone_w1`（47 条 twin-body `*_discharged` 根逐字合取，top3
  GSXRFWM/JKQEWGV2/JKQEWGV3 全接入；21 条裸 sorry HOLD 桩按 LEDGER 留下）+ Assembly
  `textCapstone` 一行 rewire。**SORRIED 112 → 135 是设计内收益**（树越大越好口径）：24 条
  锥外 discharged 债显形为锥内直源，逐根新直源表在 lane DELIVERY §4，锚 = 各出口
  docstring + LocalConcl LEDGER (c)/(d)。
- **`pa16-qzyzmjc`**（`2dea72f0`）：`QZYZMJC` 真证出列（连带私有巨件 `mcellSetNotEmpty`
  翻绿标准三）；axiom 面如实带 sorryAx（继承锥内既有链）。`GRUTOTI1_concl` 未闭合
  （Lane-draft 归档，见 `docs/lane-archives/pa2-grutoti1-concl/`）。
- **仪器事故与修复**（queue 续 261 详载）：Assembly 级模块闸 `lake build Kepler.Assembly`
  会触发 Interval.Cases shard 全量重编（几千文件）——闸被掐后遗留 12 个 shard olean 缺失；
  修复 = 6 路并行独立 `lean -o` 重编（0 error）+ Assembly.olean 独立重建（c1 等价手核路线）。
  **纪律新增：Assembly 级模块闸永久禁用。**

### 基线 F：hypermap 章结论根物化 `5bf11a82`（cone 不动，union 账本移动）

| 指标 | 值 |
|---|---:|
| K_REACH（e2e 锥） | **2,079,707（较基线 E ±0，仪器重跑逐位）** |
| K_SORRIED | **135（±0）** |
| K_AXIOM | **624（护栏不动）** |
| K_MODULES | 4,179（±0——HypermapConcl 不在 Assembly 闭包） |
| K_UNIVERSE | 2,094,333 |
| union 根 ROOTS | **157 → 162**（+5 章根） |
| ORPHANS_TOTAL（union 账本） | **13,580**（Hypermap 模块 1,299 → 156，出榜） |

- 落库内容（`hypermap-root-w1`，闸 GATE-PASS）：新文件 `Kepler/Text/HypermapConcl.lean`
  68 行——HOL `more_tame_concl.hl` 五章别名 verbatim 正名（陈述逐字取 Hypermap.lean
  原签名，体 = 原常数应用，零 sorry 纯 Mathlib）+ `Kepler.lean` +1 import + 两脚本
  手工根清单 +5。五根 `#print axioms` 全标准三零 sorryAx。
- **★ 记账勘误（仪器事实，续 266 详载）**：官方 K_REACH 仪器
  `e2e_reach_map.lean` 只 import `Kepler.Assembly`、单根 e2e，量的是**锥**；侦察的
  "+1,143" 是 **union 口径**（章根账本）增量。编排者此前（续 264 与落库 commit
  message）把它记成 cone 预期——勘误：**本波 cone +0（设计内：无消费边不造边，真
  消费点 = §2-16 TameSpine 接入 discharge），union 账本 ORPHANS −1,143**（Hypermap
  模块 1,299→156 之差逐位吻合）。union 侧读数：五根逐根 SORRIED/AXIOM 全 0；WIRE
  逐根 AQIUNPP1 1,046 / QRDYXYJ 886 / STKBEPH 203；UNION K_SORRIED_TOTAL 171
  （锥 135 + shim 36，与 la35 侦察参考线一致）。孤儿榜新 #1 = LA35 741（下一发
  `la35-root-w1` 在飞），#2 CertTM 618（根候选归档待重锚，续 265）。
- TSV（锥口径）内容与基线 E 相同，未重生。
- GATE_ROOTS 分层实例：本 kit 动了 `Kepler.lean` → 宇宙根 olean 过期，
  `lake build Kepler` 3.3 s 重建（全缓存，非重型）；成规则待办。

### 基线 G：island-wire-w1 `d607cf48`（PA23 入两宇宙，锥不动）

| 指标 | 值 |
|---|---:|
| K_REACH（e2e 锥） | **2,079,707（较基线 F ±0）** |
| K_SORRIED / K_AXIOM | **135 / 624（±0）** |
| K_MODULES | 4,179（±0） |
| K_UNIVERSE | 2,094,648（+315 = PA23 自身声明入宇宙） |
| union `GRUTOTI1_concl_discharged` 根闭包 | 58 → **2,149**（+2,092；direct-sorry 1→0） |
| ORPHANS_TOTAL（union） | 13,580 → **13,559（−21）** |

- 落库 = REWIRE：`GRUTOTI1_concl_discharged` 体 `GRUTOTI1_concl_p24_pub` → `PA23.GRUTOTI`
  （三方在库锚；2026-10-12 起只差项层执行的「直接改名」）。8 文件诚实 NO-GO
  （Text.LP 项层化被显式排期 = Assembly:6915 NEEDS；PA19 的 scout 锚过时被勘误——
  09-29 已经 `PackingJGXZYGW` discharge）。axiom 面 `[propext, sorryAx, choice,
  Quot.sound]` 新旧 footprint 逐位同（taint 来源 PA2 接口 → PA23 上游链）；
  UNION K_SORRIED_TOTAL 171 不变。
- 诚实注记：根闭包 +2,092 但孤儿账只 −21——闭包新增大半本就经其他根可达；
  PA23 入宇宙 376 件（61 件余孤儿）。事故记录：车道 farm 符号链接回填时 `cp`
  两次短暂写穿共享 `PackingConcl.olean`，落库闸 rule 4 lake 重编自愈，读数无漂移。

### 基线 H：la35 71 出口入锥 + pa15 五源闭（`a8e35ccf` + `38aa0981`）

| 指标 | 值 |
|---|---:|
| K_REACH（e2e 锥） | **2,079,940（+233，归 la35）** |
| K_SORRIED | **135（±0——pa15 所闭 5 件不在锥直源之列，诚实修正车道预期）** |
| K_AXIOM | **624（护栏不动）** |
| K_MODULES | 4,179（±0） |
| K_UNIVERSE | 2,094,451（★ 较 G **−197 异常**，仪器待查，见下） |
| ORPHANS_TOTAL（union） | 13,559 → **13,129（−430）** |
| LA35 模块孤儿 | 741 → **353** |
| 孤儿榜新 #1 | `Interval.CertTM` 618（根候选待重锚，续 265） |

- **la35-root-w1**：`la35_wire_capstone_w1` 71 出口逐字合取（生成器机械抽签名，每支带
  LA35 行号 + HOL 锚注释）+ `localconcl_wire_capstone_w2` 保型转发 + Assembly
  `textCapstone` 一行 re-point（`.1` 投影语义不变）。**cone 实增 +233**（侦察上界
  +453 对应 88 支；差 = 17 支诚实机械剔除：12 支引 LA35 `private def`、2 支
  def-Prop、3 支宇宙多态）。w1 恰标准三；w2 结构性带既有 cone sorryAx（引 S1
  capstone 所致，零新增债，Assembly warning 82/82 逐位）。
- **pa15-residual-w1**：PA15 own-sorry 5→0（`CARD_BOUNDARY_INT_BALL_BOUND_1` 新短证
  ~95 行、`_1` 版 25 行推论、`MCELL_ID_MXI` self-copy、`CARD_EDGEX_LE_16` /
  `BOUND_GAMMA_X_lmfun` self-copy PA18 真证 kit——p18 private 件以 PA15 自有已证件
  替代，未改 PA18 一字），删除面恰 5 行裸 sorry，5 件全标准三。**cone SORRIED ±0**：
  这 5 件本就不在 135 直源之列（与车道「下游不引 PA15 源」的消费者链分析互证）——
  真债已闭但记模块/union 账。
- **★ 仪器待查**：K_UNIVERSE 2,094,648（G）→ 2,094,451（H）呈 −197，与单调预期
  矛盾（期间应只增不减；E/F 期该数曾跨运行稳定 2,094,333）。cone 主指标
  （K_REACH/SORRIED/AXIOM）干净且双仪器一致（union 仪器 e2e 根行逐位同）。疑点
  指向 PA23 入宇宙窗口的 olean 版次——列入仪器随访。
- 落库过程注记：Assembly.olean 独立重建回灌主 `.lake`（18:24 版本未含 re-point，
  不重建则地图看不到 la35 增量——实测证实，c1 等价手核先例）；pa15 闸级联
  LocalConcl 重编通过；rule 1 一次撞「apply→gate 与并行 commit 的时序竞态」，
  commit 后重跑 PASS。

### 基线 I：grutoti1-d-w1 `e561b60e`（GRUTOTI1 路线 (d)，cone +334 / SORRIED −1）

| 指标 | 值 |
|---|---:|
| K_REACH（e2e 锥） | **2,080,274（较基线 H +334）** |
| K_SORRIED | **134（−1：`GRUTOTI1_concl` 出锥）** |
| K_AXIOM | **624（护栏不动）** |
| K_MODULES | **4,180（+1：PA23 成为树可达模块）** |
| K_UNIVERSE | 2,094,451（与 H 持平——基线 H 的 −197 异常未复现，仪器随访降级为观察项） |
| UNION K_SORRIED_TOTAL | 171 → **170** |
| ORPHANS_TOTAL | 13,129 → **13,130（+1 = `GRUTOTI1_concl` 本尊出锥后入孤儿账）** |

- 落库（REWIRE 双闸：PA16 THM=`KIZHLTL4`、PA24 THM=`GRUTOTI1_concl_p24_pub`）：
  PA2 `GRUTOTI1_concl`（PA2:5843，SORRIED 135 成员）的两处 term 消费者 re-point →
  PA23 已证 capstone `GRUTOTI`——PA16:2229（KIZHLTL4 内，+1 import）+ PA24:13332
  （shim，+1 import，NEEDS→DONE）。**KIZHLTL4 与 p24_pub 公理面 sorryAx → 恰标准三**
  （其唯一 sorryAx 通路即 GRUTOTI1_concl，taint 源清空）；消费者清零验证；p24_pub
  零消费者零触碰；PA2 零改动。PA24.olean 单独回灌（闸只编 $FILE 模块，不回灌则
  地图读旧 shim——la35 课再验）。
- **诚实修正**：预测 "~2,0xx 入锥" 实际 **+334**——GRUTOTI 子树大半闭包本就在锥内
  （与基线 G 根闭包 2,149 的 union-fresh 口径差异同源）。+334 仍为今日最大单笔
  （> la35 +233）。GRUTOTI1 saga 终章：PA2 路线 (a) 的 28K 行复制 kit 未走通的路，
  消费者改线一行走通（PA24:13316 NEEDS 原文 "the parallel Auto23 lane owns the
  proof (already proved)" 自证的等待）。
- 遗留卫生项：PA2 的 `GRUTOTI1_concl` 死债声明（无消费者、SORRIED 账外）可由
  卫生波删除（rule 2 裸 sorry 删除合法）；低优先。
- viz 同代重建：17,452 节点（+334 逐位）/ 204 模块 / sorry=134。

## v2.2 仪器校准：`.lake` 污染与 scratch farm（2026-11-03）

**症状**：直接拿主仓现成 olean 跑 e2e 会读到 `SORRIED 129`，而 HEAD `5384f11d` 的
TSV 是 123。原因不是脚本，而是**共享 `.lake` 被并行车道的 REWIRE/Stage-1 闸测试污染**：

- `lean/.lake/build/lib/lean/Kepler/Text/PackingAuto25.olean`（11:52 重建）里是
  `rdwkarcConcl_pc` 体，而当时 HEAD 源仍是 `RDWKARC_concl`（源 11:53 被回滚）；
- `Kepler/Assembly.olean` 也可能是闸测试态而非 HEAD 态。

**修复（standalone，禁 lake）**：在仓外建 scratch farm，硬链接镜像 `.lake` 的 Kepler
olean，然后用 `git show <ref>:<path>` 的源重建被污染模块：

```bash
REPO=/Users/zhangzhuo/repos/kepler-conjecture-lean4
LP=$(cat /tmp/lfainteg/asm_check/leanpath.txt)
FARM=/tmp/reachfarm
mkdir -p $FARM/lib $FARM/build/Kepler/Text
# 1) 镜像（硬链接，不动 .lake）
cp -Rl $REPO/lean/.lake/build/lib/lean/Kepler $FARM/lib/Kepler
cp -l  $REPO/lean/.lake/build/lib/lean/Kepler.olean $FARM/lib/Kepler.olean
# 2) 从 git 源（不是工作树）导出被判污染的模块
cd $REPO
git show 5384f11d:lean/Kepler/Text/PackingAuto25.lean > $FARM/build/Kepler/Text/PackingAuto25.lean
git show 5384f11d:lean/Kepler/Assembly.lean        > $FARM/build/Kepler/Assembly.lean
rm -f $FARM/lib/Kepler/Text/PackingAuto25.olean $FARM/lib/Kepler/Assembly.olean
cd $FARM/build
LEAN_PATH=$FARM/lib:$LP lean -o $FARM/lib/Kepler/Text/PackingAuto25.olean Kepler/Text/PackingAuto25.lean
LEAN_PATH=$FARM/lib:$LP lean -o $FARM/lib/Kepler/Assembly.olean Kepler/Assembly.lean
```

> 注意：镜像文件是 `.lake` 的**硬链接**，必须先 `rm` 再让 `lean -o` 写新文件，
> 否则会写穿到主仓 `.lake`。PA25 编译 ≈21 s，Assembly ≈32 s（本机）。

## v2.3 运行命令（standalone，不用 lake）

```bash
REPO=/Users/zhangzhuo/repos/kepler-conjecture-lean4
LP=$(cat /tmp/lfainteg/asm_check/leanpath.txt)
FARM=/tmp/reachfarm/lib        # 见 §v2.2；HEAD 态 olean farm
cd $REPO

# 默认根 = e2e
LEAN_PATH=$FARM:$LP nice -n 19 lean lean/scripts/e2e_reach_map.lean > /tmp/reachmap.out

# 任意根（环境变量 REACH_ROOT）
LEAN_PATH=$FARM:$LP REACH_ROOT=Kepler.Text.OXLZLEZ \
  nice -n 19 lean lean/scripts/e2e_reach_map.lean > /tmp/reach_oxlzlez.out

# 节点表（TSV，2M 行；见 §v2.4）
LEAN_PATH=$FARM:$LP DUMP_TREE=1 \
  nice -n 19 lean lean/scripts/e2e_reach_map.lean > /tmp/e2e-tree.tsv
```

读数时间（本机，2.08M 节点）：`reach` ≈ 95–100 s；`K_UNIVERSE` 的
`env.constants` 全扫描 ≈ 7 min（解释器逐项 fold，脚本默认执行；`DUMP_TREE=1`
时跳过）。`IO.monoMsNow` 在 `CoreM` 里返回 0（已知坑），计时请用 shell `time`。

## v2.4 DUMP_TREE 节点表（页面树数据）

`DUMP_TREE=1` 输出 `--- TREE ---` 段（TSV，首行表头）：

| 列 | 含义 |
|---|---|
| `name` | 声明全名 |
| `module` | `moduleOf`（`getModuleIdxFor?`；缺失时退化为名字前缀） |
| `kind` | `theorem` / `def` / `axiom` / `opaque` / `quot` / `induct` / `ctor` / `rec` |
| `directSorryAx` | 值里**直接**含 `sorryAx` |
| `parent` | 首次访问的父声明（根为空） |
| `childCount` | 值里 Kepler 直接依赖的**原始出现次数**（重复常量计多次） |
| `extCount` | 值里非 Kepler 直接依赖的出现次数 |
| `depth` | 首次访问深度（DFS 栈序，不是最小 BFS 深度） |
| `generated` | 机械证书层：模块名含 `Interval.Cases` / `Graphs.CertShards` / `Shard` / `CertTri|Quad|Pent|Hex`，或名字含 `_native_decide` |
| `treeChildCount` | 以本节点为首次父的子节点数（树边） |

同一段前还有两个模块聚合表：`--- MODULE TOP30 BY NODES ---` 与
`--- MODULE TOP10 BY SORRIES ---`（列：module / nodes / sorries / maxDepth / generated）。

---

# 归档：v1 地图（2026-10-22 ～ 2026-11-02）

> 以下为 v1 口径历史读数（旧指标 = SORRIED / 可达声明 / 可达公理），保留作审计；
> 其中「可达 Kepler 声明」用旧计数，不可与 v2 的 K-REACH 直接比较。

## 0. 头版

### 2026-10-26（上午，续 5）刻度（池C-W2 落库 `621a7566` 后重生成，TSV `bfe278b5`）

| 指标 | 值 | 变化 |
|---|---:|---|
| 直接 sorryAx 债务源 | **152** | −1：PA25 `K3_CC_WI_ALT`（parent `cc_4_cc_ke4`）出列——池C-W2 四件标准三（MCELL3_DIHX / WEDGE_UNIQUE_CC_CELL / K3_CC_WI_ALT / K3_CC_WIM_ALT）。diff 恰此一行删除、零新增 |
| 可达 Kepler 声明 | 218,326 | +29 |
| 可达 Kepler 公理 | 624 | 0 |

### 2026-10-26（上午）刻度（池C 落库 `db3ae79f` 后重生成，TSV `09f84c2e`）

| 指标 | 值 | 变化 |
|---|---:|---|
| 直接 sorryAx 债务源 | **153** | −2：PA25 `LEAF_RANK_REUHADY`（parent `c_4_azim_mcell_dih_y`）、`MCELL4_FULL_WEDGE`（parent `cc_4_cc_ke4`）出列——池C 五件标准三（REUHADY / MCELL3_DIHX_POS / LEAF_RANK_REUHADY / MCELL4_DIHX_AZIM / MCELL4_FULL_WEDGE）。diff 恰为此两行删除、零新增 |
| 可达 Kepler 声明 | 218,297 | +654（池C 新证明体 + PA24 `REUHADY_p24` 闭包入锥；W5a LA9 / W2 AzimBridge 不在锥内，零影响） |
| 可达 Kepler 公理 | 624 | 0 |

> 本日同批落库但**锥刻度 0** 的波：WSEWPCH W5a（LA9 四件，`b1e1224d`）、W2（AzimBridge 20 件，`057a0683`）——
> 它们是 W6 收官的前置资产，锥 +1 要等 TameLp 处 WSEWPCH 本体闭合才兑现。

### 2026-10-26（凌晨）刻度（TSV `cc3cb531` 后重生成）

| 指标 | 值 | 变化 |
|---|---:|---|
| 直接 sorryAx 债务源 | **155** | −1：PA3 `GRHIDFA_concl`（GRHIDFA W5 capstone + 九桩回填后出列，PA3 全模块归零）。diff 仅此一行删除、零新增 |
| 可达 Kepler 声明 | 217,643 | +315（GRHIDFA/FCHKUGT 五波私有 kit 入锥） |
| 可达 Kepler 公理 | 624 | 0 |

> **口径注**：PA3 文件级 bare sorry 9→0 是**文件刻度**；e2e 锥只记 `GRHIDFA_concl` 一个直源
> （其余八桩只被它消费、不被 Assembly 锥直达），故锥刻度 −1 而非 −9。此前 priority-queue
> 预告"−9 计分"系混用两种刻度，已更正。

| 指标 | 2026-10-22 | 2026-10-25 | 变化 |
|---|---:|---:|---|
| 可达 Kepler 声明 | 8,305 | **217,328** | +209,023（nli A1 把 CFWGKMBZ 证书接入 Assembly，证书闭包 ~206k 声明进锥；另加 PA25/PA15/PA11/N2 证明体；2026-10-23/25 填证连带 +825 私有 kit 声明入锥。全部内核检查、零新公理） |
| 直接 sorryAx 债务源 | 149 | **156** | 净 +7 = **真闭 −29 / 暴露 +36**。真闭：日间 −16（euler PA21 `mi_gamma3f`、P0 PA10 `RVFXZBU`、B3 `YIFVQDV_1`+`QZKSYKG1`、B4 `QZKSYKG2`、B7 `DDZUPHJ`、B8f `SLTSTLO2`、nli A1 `nliRestFWGKMBZ`、PA25 `cc_bool_model_data`、nli N2 `nliRest6096597438b`、PA15 `MCELL_ID_MXI_2`+`MCELL_ID_OMEGA_LIST_N`+`DIHX_SYM`、PA11 `k2Case`+`k3Subset`+`rogersInterVLemma`）；−2 TameLp `sum_tauVEF_upper_bound`、PA18 `cc_pe_exists`；−1 ContraFan `LEMMA_4_POINTS_FINAL`；−2（10-24）TameLp `ineq_tau3`、PA18 `pa18_ccCell_swap`（SF-50）；**−7（10-25 日间）：TameLp `ineq_tau{4,5,6}_tauVEF_std`（ykit10 装配）、PA25 `K4_CC_WI_ALT` / `MCELL4_AZIM_LT_PI` / `CC_CELL_WEDGE_MATCH_UH`（池A/池B 收割）、LA16 `JEJTVGB_p16`（三件套 HOL 忠实装配）；−1（10-25 晚）：PA21 `TSKAJXY_034`（Euler W1-W5 五波 + SF-51 双清偿后一行翻除，`#print axioms` 全净标准三，PA21 归零）**。**暴露 +36（10-25）：`JEJTVGB_p16` 翻除后其证明体消费 LA1 注册表 22 条 `*_concl` 条件箭头（全部 `:= sorry` shim）+ LA20 `AQICLXA`/`FZIOTEF`/`SCS_6I1_BERAK_BY_CSTAB` + LA22 `OCBICBY_p22`/`is_scs_3{M1,T1,T5}_p22` + LA23 `LFLACKU_p23`/`s_init_list_alt_p23` + LA24 `XWITCCN_CASE_{3,4,5,6}_IS_SCS_p24` + LA27 `EAPGLE_p27` + LA1 `WKEIDFT_concl`——这些债此前全被单个 shim `JEJTVGB_p16` 遮蔽，现按真实粒度入账（四单源侦察 §3.5 预判"只是把 SORRIED 换了个名字"，实测是换成了 36 个名字）。** |
| 可达 Kepler 公理 | 624 | **624** | 0（全部 `native_decide` 图 shard；interval 证书用内核 decide，不新增公理） |

**结论：主定理当前的实际债务源是 156 个声明（2026-10-25 晚 TSKAJXY_034 翻除后地图重生成；本行 diff 仅一行删除零新增）。等效口径：若不计 JEJTVGB 翻除暴露的 36 个上游 shim，与前版可比的数字是 128 − 8 = 120。** AJRIPQN 的五个名字
（`QZKSYKG1` / `QZKSYKG2` / `SLTSTLO2` / `DDZUPHJ` / `YIFVQDV_1`）、nli
`nliRestFWGKMBZ`/`nliRest6096597438b`、PA25 `cc_bool_model_data`、PA15
`MCELL_ID_MXI_2`/`MCELL_ID_OMEGA_LIST_N`/`DIHX_SYM` 与 PA11
`k2Case`/`k3Subset`/`rogersInterVLemma` 已从清单消失；
`#print axioms Kepler.Text.AJRIPQN` = `[propext, Classical.choice, Quot.sound]`。

> **PA25 口径注**：`cc_bool_model_data` 的证明体已无 `sorryAx`（`#valax3`
> 证明调用图 19,858 节点，仅标准三），故地图按其值把它移出 source。但它的
> 冻结陈述类型经 `cc_data_v8 → ccCell → ccUh → cc_uh_exists → cc_pe_exists`
> 仍触达 PA18 既存 sorry，因此字面 `#print axioms cc_bool_model_data` 仍会
> 打印 `sorryAx`；该类型债由 **`cc_pe_exists` 自身**作为独立 source 记账，
> 未被掩盖。（**2026-10-23 晚更新：`cc_pe_exists` 已真证并入仓，此类型债
> 随之清除；2026-10-24 SF-50 又删去 PA18 唯一残余 private 假陈述
> `pa18_ccCell_swap`（机检 4 片反例为假；根因 CFFONNL 前提误植，复 HOL 原序
> 后 `absurd` 直闭），PA18 全模块 direct 源归零。`cc_bool_model_data` 的
> axiom 面是否已转净以 `#print axioms` 实测为准。**）闸的 rule 5 自
> 2026-09-28 起本就允许 `sorryAx`。

## 1. 债务源按模块

| 模块 | direct sorry 源 | 代表声明 |
|---|---:|---|
| `Kepler.Assembly` | 81 | 77 个 `nli*`（57 个父为 `nliPackNonlinearRest`、8 个 `nliTskBank`、7 个 `nliCell3Bank`、5 个直挂 `nonlinearInequalities`）+ `fcdjdot` / `jcajydu` / `tameCorrespondenceIso`（父 `textCapstone`）+ `lpArchiveCertificatesDebt`（父 `lpArchiveCertificates`） |
| `Kepler.Text.PackingAuto25` | 35 | 28 个 `real_model_*`（父 `pkrmQu/Qx/Qy` 等）+ `LEAF_RANK_PROPS` 3（`cc_prep_model_data`/`pkLeafRankAzimPointwise`/`pkLeafRankCriticalEdge`）+ `K3_CC_WI_ALT`（残 `WEDGE_UNIQUE_CC_CELL` 一债）+ `MCELL4_FULL_WEDGE` + `LEAF_RANK_REUHADY` + `ox3q1hP25`（10-25 出列：`K4_CC_WI_ALT` / `MCELL4_AZIM_LT_PI` / `CC_CELL_WEDGE_MATCH_UH`） |
| `Kepler.Text.LocalAuto1` | 23 | `main_nonlinear_terminal_v11`（109 条 Main_estimate 合取的 deliberate 外部锚）+ **22 条注册表条件箭头 `*_concl`**（`ARDBZYE`/`AUEAHEH`/`BNAWVNH`/`CNICGSF1-5`/`FYSSVEV`/`HIJQAHA`/`MFKLVDK`/`MIQMCSN`/`NWDGKXH`/`OTMTOTJ1-4`/`RAWZDIB`/`RYPDIXT`/`VQFYMZY`/`YOBIMPP`，父 `JEJTVGB_p16`；`WKEIDFT_concl` 父 `EQ_DIAG_STAB_6I1_03`）——10-25 随 `JEJTVGB_p16` 翻除暴露，均为 `(h : main_nonlinear_terminal_v11) → scsArrow …` 的 `:= sorry` shim，HOL 证体在 appendix.hl/hexagons.hl 等 |
| `Kepler.Text.LocalAuto24` | 4 | `XWITCCN_CASE_{3,4,5,6}_IS_SCS_p24`（父 `UXCKFPE_p24`，10-25 暴露） |
| `Kepler.Text.LocalAuto22` | 4 | `OCBICBY_p22`（父 `JEJTVGB_case_breakdown_p16`）+ `is_scs_3{M1,T1,T5}_p22`（父 `BKOSSGE_p16`，10-25 暴露） |
| `Kepler.Text.LocalAuto20` | 3 | `AQICLXA`/`FZIOTEF`（父 `OEHDBEN`）+ `SCS_6I1_BERAK_BY_CSTAB`（父 `OEHDBEN_PRIME`，10-25 暴露） |
| `Kepler.Text.LocalAuto23` | 2 | `LFLACKU_p23`/`s_init_list_alt_p23`（父 `JEJTVGB_case_breakdown_p16`，10-25 暴露） |
| `Kepler.Text.TameLp` | 1 | `fully_surrounded_perimeter_bound`（唯一残源，单锚 WSEWPCH 核；`ineq_tau{3,4,5,6}` / `sum_tauVEF_upper_bound` 10-23～25 全部真证出列） |
| `Kepler.Text.PackingAuto3` | 1 | `GRHIDFA_concl`（六波计划 W1 kit 28 件已入仓 18e274ee） |
| `Kepler.Text.PackingAuto2` | 1 | `UPFZBZM_concl`（架构性：PA2 被反向 import，F1 重接线已批） |
| `Kepler.Text.LocalAuto27` | 1 | `EAPGLE_p27`（父 `JEJTVGB_case_breakdown_p16`，10-25 暴露） |

**零 direct 源的关键模块**：`PackingAuto21`（2026-10-25 TSKAJXY W1-W5 五波 + Euler W1-W5 五波 + SF-51 全链闭合后归零；`TSKAJXY_034` axiom 面全净标准三）、
`LocalAuto16`（2026-10-25 `JEJTVGB_p16` 三件套 HOL 忠实装配后归零，债务下沉到 LA1 注册表与 LA20-27 scs 机器）、
`PackingAuto18`（2026-10-23 `cc_pe_exists` 真证 + 2026-10-24 SF-50 删假陈述 `pa18_ccCell_swap` 后全模块归零；10-25 `BDXKHTW`/`EWYBJUA` 双闭）、
`ContraFan`（2026-10-24 `LEMMA_4_POINTS_FINAL` 四波真证 + W4 原子接线后全模块归零；`ContraFanDeep` 全程零 sorry）、
`PackingAuto11`（LEPJBDJ 三私件后）、
`PackingAuto15`（DIHX_SYM 后）、
`PackingAuto17`（AJRIPQN 本体真装配）、
`PackingAuto13`（B8f 后）、`PackingAuto14`（B4 后）、`PackingAuto7`（B3 后）、
`PackingAuto12`、`PackingAuto9`、`PackingAuto10`（P0 后）、`PackingAuto24`、
`PackingConcl`（不在锥内）。

## 2. 最大消费簇（父边）

| 父声明 | 直接子债务源数 | 说明 |
|---|---:|---|
| `Assembly.nliPackNonlinearRest` | **58** | 非线性不等式 rest bank；A1 后 59→58，仍是最大单簇 |
| `Text.pkrmQu` | 9 | PA25 packing chapter 的 `real_model_*` 数据 |
| `Text.pkrmQy` | 8 | 同上 |
| `Text.pkrmQx` | 8 | 同上 |
| `Assembly.nliTskBank` | 8 | TSKAJXY 银行 |
| `Assembly.nliCell3Bank` | 7 | cell3 银行 |
| `Assembly.textCapstone` | 5 | `fcdjdot` / `jcajydu` / `tameCorrespondenceIso` 等 |
| `Assembly.nonlinearInequalities` | 5 | 六分量接口直挂节点 |
| `TameLp.MQMSMAB_adm1` | 4 | TameLp 不等式 |
| `Text.LEAF_RANK_PROPS` | 4 | PA25 leaf rank 数据 |
| `Text.pkrmAzim` | 2 | PA25 real_model 切片 |
| `Text.cc_4_cc_ke4` | 2 | PA25 cc 链 |
| 其余（MCELL2_DIHX / MCELL4_BARV_FI 等） | 各 1 | 见 TSV |

## 3. 关键结论与纠错

1. **AJRIPQN 已归零（2026-10-23）**：四个承重根
   `QZKSYKG1`（B3 `ce71abd3`）、`QZKSYKG2`（B4 `c7b67c9b`）、
   `DDZUPHJ`（B7 `c8b43895`）、`SLTSTLO2`（B8f `cb268b64`）全部真证；
   `#print axioms Kepler.Text.AJRIPQN` = `[propext, Classical.choice, Quot.sound]`。
   `WQPRRDY`（PA7:3976）仍是 sorry，但 B4 证明 QZKSYKG2 时不消费它，
   已退出 e2e 锥。
2. **首个 nli rest 源接线（nli A1 `286d11b8`）**：`nliRestFWGKMBZ` 由
   `Kepler.Interval.Cases.CFWGKMBZ`（605 分片 + Base，205,418 叶，探针标准三）
   直接导出；证书闭包 ~206k 声明进入锥，但**零新公理**。这是 57 个
   `nliPackNonlinearRest` 源的可复制样板（A2 rest 9 含 sqrt/atan/ite，
   不能照搬 glue，且冷构建外推 40–45h）。N2 rest 1 先用 hybrid sin 编码 +
   CertGD/BBTreeGD 绕开损坏的 CertG，达到 78 叶闭合。
3. **PA10 `RVFXZBU` 已由 P0（`760a192a`）解决**：PA25 `MCELL4_BARV_FI`/
   `MCELL4_LEAF3` 改接 PA14 `RVFXZBU_p14`，PA10 源已离场（PA20 的两处消费
   不在 e2e 锥）。
4. **PA24 / PackingConcl 零可达**：仍是邻近的 pack_concl 合并层，
   不在当前 e2e 锥；REUHADY1(d) 不阻塞当前主定理。
5. **最大的下一块是 Assembly 的 57 个 `nliPackNonlinearRest` 源**；
   其次是 PA25 的 38 个源（28 `real_model_*` + 10 其他）。
6. **624 条公理 = 23 条 `Assembly.GoodListShard*` + 601 条
   `Graphs.CertShards.*`/`CertTri/Quad/Pent/Hex`**，全部 `native_decide`
   生成，模块分布见 §4，与 DEBT 脊柱探针的 624 完全一致。
7. **口径警告**：可达声明数从 8,305 跳到 216,032 不是债务增加，而是
   CFWGKMBZ 证书（内核可检查的 shard 树）进入了证明项闭包；比较债务时
   看 direct sorry 源（130）与公理（624），不要看可达声明总数。

## 4. 624 条可达公理的模块分布

| 模块族 | 公理数 |
|---|---:|
| `Kepler.Graphs.CertShards.HexR*` | 224 |
| `Kepler.Graphs.CertShards.Pent*` | 202 |
| `Kepler.Graphs.CertShards.Quad*` | 95 |
| `Kepler.Graphs.CertShards.Hex*` | 66 |
| `Kepler.Assembly.GoodListShard*` | 23 |
| `Kepler.Graphs.CertTri/Quad/Pent/Hex` | 21 |
| **合计** | **624** |

全部名称含 `_native.native_decide.ax_1_1`，无其它非标准公理。

## 5. 口径与再生成

- 静态 proof-term 遍历；`ConstantInfo.value? true`（theorem/opaque 值都展开，
  与 `#print axioms` 的闭包一致）。
- 只统计**直接**含 `sorryAx` 的声明；间接 taint 通过父边体现。
- 父边是第一个 BFS 父，不是唯一父；一个源可在多条路径上。
- 证明项里的死分支也会被计入（与 `#print axioms` 一致，因为内核仍要检查）。
- 再生成：见顶部 §v2.2/§v2.3（standalone + scratch farm；**不再使用 `lake`**）。
  v1 曾用 `cd lean && lake env lean scripts/e2e_reach_map.lean`，该命令已废弃：
  它依赖 `.lake` 共享状态，会被并行车道污染（2026-11-03 事故，见 §v2.2）。
  每次落库后重跑并 diff SORRIED 清单，就是最直接的 e2e 债务刻度。

## 6. 建议的下一步

1. **P0 — nli 样板复用**：把 A1 的“证书 → `CFWGKMBZ_pos` → Assembly glue”
   固化成模板；A2（rest 9，2,775 分片/96 万叶）先解决预构建 oleans/分机，
   再接线。
2. **P0 — 624 公理 manifest + 抽样 replay**（审计文档 P0 第 2 项）。
3. **按簇派工**：58 `nliPackNonlinearRest` → 39 PA25（28 `real_model_*`）→
   8 `nliTskBank` → 7 `nliCell3Bank`。
4. **LP 端到端审计**：在填 `lpArchiveCertificatesDebt` 之前完成
   （`leanprover/lp-verify` + 原始 `formal_lp` 证书，见
   `docs/scouts/lean4-ecosystem-scout.md`）。
5. **WQPRRDY 记账**：PA7:3976 仍是 sorry 但不在锥；若未来有消费者，
   会被拉回地图，届时按 B4 的 private kit 逐 k 处理。

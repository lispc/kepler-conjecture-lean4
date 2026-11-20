# 585 信任基座与纯标准三 —— `notame7` 可证剪枝路线

> **P0 结果（2026-11-20，`notame7-census-w1` 收线，pq §8 续1326）：按本文 §5 停机闸判停，不升级 P1/P2。**
> 剪枝因子实测 Tri **1.68×**（可剪占比 40.40%）/ Pent **1.96×**（48.98%），远低于 20–30× 复合闸；
> 机制性原因：notame7 命中 100% 落 C 款（squander 预算耗尽），而预算边界在树中后段才穿过
> （命中深度 13–20/21）——树已基本生成故剪枝弱；达闸需命中率 ≥95–97%。剪枝 soundness 的
> 实证侧全绿（终图集逐根完全相等）——**路线数学成立，收益不成立**。附带发现：343/7,263
> Pent 死根（4.72%，全 C 款）= 「1 pop 快速件」候选，未剪枝闭包规模未测未折算。

> **性质**：战略研究结论，不是实时账本，也不是已完成的内核化证明。
> 日期：2026-11-20；写作时 HEAD：`37ef8aac`。
> 挑战/补充对象：`docs/trust585-kernelization-report.md`。
> 实时公理面与 `sorryAx` 分解仍以 `docs/priority-queue.md` 文件头及
> `docs/e2e-reachability-map.tsv` 为唯一出处，本文不另存实时状态数字。
>
> 证据标签：**SRC** = 本地源码/原版直接证据；**MEA** = 仓内已有实测；
> **EST** = 明确假设下的成本换算；**UNRESOLVED** = 尚未完成机器验证。
> 本轮独立复核未修改 Lean 源码，未启动新的 Lean 编译、证书农场或全量重放。

---

## 0. TL;DR

1. **朴素地把 580 条 shard-range 的 `native_decide` 改成 `decide`，本机 NO-GO。**
   已有内核成本与内存实测足以否定这条具体路线。
2. **但“580 → 0 整体 NO-GO”证据不足，应改判 UNRESOLVED。** AFP 的约 18.7 亿次
   扩展是当前枚举算法的工作量，不是所有形式证明都必须支付的数学下界。
3. 新发现的具体突破口是：库内已有的 `inv_notame` / `untame_notame` 允许对当前已满足
   `notame7` 的非终图**剪掉整个后裔子树**，并保持所有 tame 终图的可达性。
   这不是改陈述，也不是猜想中的“信任洗白”；通用正确性胶水可以复用现有归纳模板。
4. 辅助杠杆也尚未计价：AFP 的 `enumTab` 缓存未移植，而本仓已有
   `enumerator_equiv` 候选正确性/完备性定理。现有每 pop 成本不是优化后的下界。
5. `tri_shard_3/4` 仍适合作为快速减项；`tri_shard_0/1/2` 的“约 26 核时、1–2 天”
   是可复核 Lean 实测之前的 EST，不应先据此启动专用证书工程。
6. 默认 `bv_decide` 与 `native_decide` 一样经 `nativeEqTrue` 加公理，直接换皮无收益；
   但 Core/Mathlib 的内核 LRAT 检查器仍可用，不能把“默认 tactic 加公理”误写成
   “所有 SAT/LRAT 证明都不能标准三”。
7. 即使图枚举的 585 条全部退出根面，终根纯标准三仍要求另行清除全部 `sorryAx`；
   其当前数量与 Text / Assembly 分解只引用 `docs/priority-queue.md`。

---

## 1. 结论的准确边界

### 1.1 可以确认的判断

- **逻辑与工具层面没有“额外公理不可消除”的障碍。** 对封闭可判定事实，
  `decide +kernel` 或“已证 soundness 的反射检查器 + 内核证书检查”都能提供标准三证明。
- **直接全量重放不可行。** 既有 Hex 微探针给出 42–61 ms/pop；单 root/单 shard 的
  朴素 `decide` 还出现超过 14 GB 且持续增长的 RSS，见 `docs/heavy-scout.md` §4–§5
  与 `~/c17_backup/lane_snapshots/kernel-decide-pilot/DELIVERY.md`。
- **原生分片陈述的固定 fuel 等式不是唯一可攻击接口。** 根定理只关心最终分类结论；
  可新增证明用后继关系和闭包证书，再改写 `tame_classification` 的证明体，陈述不动。

### 1.2 尚不能承诺的判断

- 尚不能承诺 585 → 0 的总墙钟、总核时、证书体积或最终成功率。
- `notame7` 在真实闭包中的占比、剪枝后的 pops、每 live pop 成本与 RSS 均未测。
- 本轮没有新增 `#print axioms` 输出；任何后续“已减少公理”的声明都必须附对应命令的
  编排者亲跑输出。

---

## 2. 原报告哪些成立，哪些需要修正

### 2.1 成立：默认 native 求值确实引入额外公理

本机 Lean 4.32.2 的 `Lean/Meta/Native.lean` 明确说明 `nativeEqTrue` 编译并运行闭项，
随后添加一条断言该闭项等于 `true` 的公理；`native_decide` 与默认 `bv_decide` 共用此机制。
因此：

- 把 585 条 `native_decide` 直接改名为 `bv_decide`，不会减少信任或公理数量。
- 隐式 per-use 公理还会削弱现有 manifest 的可见性，不应采用。
- Lean 官方对 `#print axioms` 与 native evaluation 的说明见
  <https://lean-lang.org/doc/reference/latest/ValidatingProofs/>。

### 2.2 过强：18.7 亿次扩展不是证明论下界

`reference/afp-flyspeck-tame/ArchStat.thy:59-72` 的计数来自当前 `next_tame` 工作列表
算法。它准确描述了**重放这个算法**的规模，却不排除：

- 利用已证不变量删除不可能产生 tame 终图的整个子树；
- 用等价但更适合内核的枚举器、缓存或打包表示；
- 用通用数学定理替代对大量同构/同类计算的逐项展开。

因此，由该计数只能推出“朴素全量重放昂贵”，不能推出“任何标准三证明都必须逐个
检查这些结点”。

### 2.3 过强：SAT/LRAT 不是工具端整体判死

默认 `bv_decide` 的确走 native 收口；但 Core 还暴露：

- `Std.Tactic.BVDecide.LRAT.check_sound`；
- `Std.Tactic.BVDecide.Reflect.verifyCert_correct`；
- Mathlib `Mathlib.Tactic.Sat.FromLRAT` 的 `lrat_proof`。

证书检查等式可以改由 `decide +kernel` 证明，而不调用默认 `nativeEqTrue`。
不过当前本体是 List/Nat 上的确定性图枚举，不是天然的小 CNF；朴素 bitblast 很可能
比专用反射检查器更贵。**LRAT 保留为局部有限子问题工具，不作为首选主线。**

### 2.4 Tri 的快速件与估算件必须分开

- `tri_shard_3/4`：离线探针显示各 1 pop、无子代，直接 `decide` 是高置信度小试验；
  尚需 Lean 编译与公理面验收，不能把离线结果记作已经 −2。
- `tri_shard_0/1/2`：26 核时来自旧估算；主研究文档明确零 Lean 编译，Python 的
  约 0.1 ms/pop 也不是 Lean native/kernel 测量。先定标，后承诺排期。

---

## 3. 核心新路线：`notame7` 整棵死子树剪枝

### 3.1 当前枚举留下的空隙

`lean/Kepler/Graphs/TameEnum.lean:15-17` 中：

```lean
def next_tame (p : Nat) (g : Graph) : List Graph :=
  (next_tame0 p g).filter (fun g' => !g'.final || is_tame g')
```

完整的 `is_tame` 过滤只强制于终图。非终图如果已经满足 `notame7`，仍可能进入
worklist 并继续扩展。

但库内已经有三条恰好处理这种情况的数学事实：

| 事实 | 位置 | 作用 |
|---|---|---|
| `inv_notame` | `lean/Kepler/Graphs/GeneratorProps.lean:758-840` | `notame7` 沿生成步骤保持 |
| `inv_inv_notame` | 同文件 `:843-850` | 可直接用于路径归纳的不变量形式 |
| `untame_notame` | 同文件 `:852-879` | 满足 `notame7` 的终图不可能 tame |
| `inv_inv_next_tame` | 同文件 `:1007-1012` | 从 `Seed` 出发提供所需 `inv` 不变量 |

所以一个已满足 `notame7` 的非终图，其所有后裔都不可能贡献最终需要的 tame 终图。

### 3.2 新增证明用后继关系，不改原定义

建议新增：

```lean
def next_tame_pruned (p : Nat) (g : Graph) : List Graph :=
  (next_tame p g).filter (fun g' => !notame7 g')
```

需要证明的通用定理形态是：

```lean
RTranCl (next_tame p) (Seed p) g →
g.final = true → tame g →
RTranCl (next_tame_pruned p) (Seed p) g
```

证明可直接仿照 `lean/Kepler/Graphs/GeneratorProps.lean:968-999` 的
`filterout_untame_succs'`：

1. `inv` 沿 `next_tame` 保持；
2. `inv g ∧ notame7 g` 沿 `next_tame` 保持，子关系经 `next_tame0_subset_plane`
   接入 `inv_inv_notame`；
3. 被新 filter 排除的子图必满足 `notame7`；
4. 若被排除结点之后还能到达终图，则该终图继承 `notame7`，由 `untame_notame`
   与 `tame g` 矛盾。

**状态：UNRESOLVED。** 数学路线与库内接口已经逐项对齐，但通用 Lean 定理尚未在本轮
编写和编译。

### 3.3 如何接入终定理而不改陈述

`RelativeCompleteness.completeness` 本来就以 `tame g` 为假设，见
`lean/Kepler/Graphs/RelativeCompleteness.lean:169-181`。可以：

1. 用现有 `TameEnum_comp` 先得到原 `next_tame` 可达性；
2. 用上述剪枝保持定理转成 `next_tame_pruned` 可达性；
3. 对每个 seed 提供剪枝闭包的 `checkFinal` 证书，仍复用 `loop_some_true` 和
   `checkFinal_correct`；
4. 以新的完备性装配证明替换 `lean/Kepler/Graphs/TameClassification.lean:23-25`
   的**证明体**，保留 `tame_classification` 的陈述逐字不动。

这样旧 585 条可保留为 native 交叉校验，却不再进入终定理依赖。若目标只是
`#print axioms` 恰为标准三，未使用的旧公理不会出现在结果中；若还要求整个源码树
不存在旧 `native_decide`，可在新证明验收后再删除或改造旧证书，二者不要混为一谈。

---

## 4. 辅助杠杆：先优化再谈全量判死

### 4.1 枚举缓存没有移植

AFP 在 `reference/afp-flyspeck-tame/Enumerator.thy:55-61` 对 `inner,outer < 9`
使用 `enumTab` 预计算表；本仓 `lean/Kepler/Graphs/Enumerator.lean:7-8,38-41`
明确没有移植，直接重算 `enumerator`。

所以 42–61 ms/pop 是当前未优化实现的数据，不是所有内核化实现的成本下界。
可新增与 `enum` 逐点相等的快速实现和相等性定理，原陈述不改；收益必须实测。

### 4.2 候选完备性已经证明，不是纯研究空白

`lean/Kepler/Graphs/EnumeratorProps.lean:609-612` 已有：

```lean
enumerator_equiv :
  is ∈ enumerator n m ↔ incrIndexList is n m
```

这把候选 membership 归约为长度、端点、界与单调性等局部条件。后续若要构造候选
前缀剪枝或快速 successor checker，可直接使用这条正确性/完备性桥，而不是从零发明
“穷尽性证书”。

### 4.3 内存墙可通过声明拆分处理

`decide +kernel` 在单个大声明中保留求值垃圾，是已有实测的重要风险；但它不是必须
一次声明跑完整棵树的理由。`lean/Kepler/Graphs/WorklistSplit.lean:13-83` 已有
`loop_mono`、`loop_append`、`loop_list_of_forall` 和 `loop_singleton_of_children`，
支持分块证明与燃料存在形装配。

因此应分别记录：

- 单声明朴素重放的内存 NO-GO；
- 分批证书的总核时与证书治理成本。

不能用前者替代对后者的测量。

---

## 5. 成本门槛：什么结果才值得全量推进

AFP 当前计数合计为 **1,870,507,512** 次扩展（SRC）。以下只是把统一平均单价乘以该数
的敏感性分析（EST），不是分类别排期；真实预算必须按 Tri/Quad/Pent/Hex 分别定标。

| 剪枝后平均内核成本 | 不减少结点时的总量级 |
|---:|---:|
| 42–61 ms/pop | 约 21,875–31,903 核时 |
| 2 ms/pop | 约 1,039 核时 |
| 1 ms/pop | 约 520 核时 |
| 0.2 ms/pop | 约 104 核时 |

剪枝比例直接除以结点量。例如若各类规则合计减少 **30×** 扩展，即使仍按旧的
42–61 ms/pop，也约为 **729–1,063 核时**（EST）。所以不需要先假设“99% 都是死支”
才值得测量；20–30× 的复合收益就可能改变决策。

反之，如果优化后仍高于约 2 ms/pop，且剪枝不足约 20–30×，则本机全量路线仍不具
吸引力，应停止扩张而不是硬造证书农场。

---

## 6. 外部先例的正确用法

`corun1024/4ct`（<https://github.com/corun1024/4ct>）展示了三点可迁移方法：

- 用已证通用 soundness 定理检查不可信生成器产出的证书；
- 用宽 `Nat` 位运算替代大量逐步 List 搜索；
- 将大计算拆成多个声明以释放内核求值内存。

但其 633 个四色构型与本仓 18.7 亿次图扩展不是同一成本单位，“633 vs 18.7 亿”不能
用来证明本问题规模差六个数量级，也不能用其约 26× 加速直接估算本仓收益。
该项目大量由 AI 生成且缺独立权威复核，只作方法论先例。

---

## 7. 建议的最小 pilot（尚未开工）

### P0：零 Lean 离线普查

- 在现有 Tri 五根统计：`notame7` 结点比例、剪枝后 pops、深度和 final 数。
- 再选一个中等 Pent 根，检验 Tri 结论能否外推。
- 输出原始日志和按类别的死因分布；不预设 99%，也不把 Python 时间当 Lean 时间。

### P1：纯符号通用胶水

- 新增 `next_tame_pruned` 与可达性保持定理。
- 做负对照：篡改 `notame7` 条件或伪造被剪枝路径时，证明/检查必须失败。
- 单文件独立编译并检查通用定理公理面。

### P2：`tri_shard_2` 端到端样板

- 原闭包 46,746 pops，适合与旧口径对照。
- 比较剪枝前后 pops、每 live pop 内核成本、RSS、证书体量与编译墙钟。
- 用分批证书和 `WorklistSplit` 装配，禁止一开始就跑 580 全量。

### P3：扩展闸

只有 P0–P2 同时给出以下证据，才讨论 Quad/Pent/Hex 扩展：

1. 通用剪枝定理真实编译且负对照有效；
2. 剪枝后的 pops 有足够下降，或优化后的每 pop 成本进入 §5 的可接受区间；
3. 分批 RSS 有界，证书可确定性再生成并可 replay；
4. 代表根的 `#print axioms` 恰为标准三。

若复合收益不足 20–30× 且成本仍高于约 2 ms/pop，停止全量计划，保留现有信任基座。

---

## 8. 最终验收

图分类侧必须先亲跑：

```lean
#print axioms Kepler.Graphs.tame_classification
```

目标为恰好 `[propext, Classical.choice, Quot.sound]`。之后终根仍须独立完成剩余
`nli*` / hLP 清债，最终以：

```lean
#print axioms Kepler.the_kepler_conjecture_e2e
```

恰好标准三为唯一验收。不得用 import 成功、离线 Python 通过或源码中不再出现
`native_decide` 代替这两条公理审计。

# shard-math-roadmap — 数学/算法层 shard 压缩路线

> 来源：`shard-math-research-w1`（2026-11-21 收线，判词 **GO（条件式）**）。
> 数字出处：快照 `~/c17_backup/lane_snapshots/shard-math-research-w1/REPORT.md`
> + `data/{inventory,cost_model,recovery_timings}.tsv` + `prototype/`；
> 账本 `docs/priority-queue.md` §8 续1366/续1367。
> 本文只给方向、裁决点与「不要再试」清单；同一指标不在此重复抄数。

## 0. 一句话

585 CertShards / Interval Cases 的压缩有三条候选：**W1** 把已证 sound 的 notame7 剪枝
放进 native 枚举（数学杠杆，改陈述）、**W2** 成本均衡合并（公理数下降，改验收口径）、
**W3** 继续 Interval cases-swap P3-GO 批（不改信任面，需批产）。四条「省总量/去重/记忆化」
路线已被机器证据关闭。

## 1. W1 — CertShards：notame7 进 native 路径（第一优先，需 SF + 用户改裁）

- **发现**：`Kepler/Graphs/TameEnum.lean` 的 `next_tame` 与 AFP 同形，只滤
  `!final || is_tame`，**不含 notame7**；notame7 普查的剪枝因子在 Tri/Pent 样本上
  [exact]，终图集逐根相等。
- **证明义务**：`GeneratorProps.filterout_untame_succs'` 的四块零件全在库
  （`inv_inv_next_plane` / `inv_inv_notame` / `untame_notame` / `next_tame0_subset_plane`），
  只缺一个 frontier-`inv` 引理（16,530 根的地面可判定事实）。
- **收益/风险**：总工作量按剪枝因子等比下降；RSS 不变（1.6 GB 导入地板）。
  但剪枝因子是「机制性平台」，其余 7,250 根未普查；需先在 2–3 个 Hex 样本补测。
- **裁决点**：改 `next_tame` = 改陈述 ⇒ **SF 通道 + 用户改裁**；重生成 580 文件 +
  coverage + 全量验收。建议先开 ≤1 车道日的**零 Lean scouting**（Hex 三样本因子），
  再决定是否发施工车道。
- **优先验证的备选（可免 SF）**：不改 `next_tame`，在 shard **证明侧**加一条
  pruned-loop ⇒ unpruned-loop 的 bridge（消费 `filterout_untame_succs'` 的 soundness
  方向），陈述保持原样、585 公理面不动；若 bridge 方向不成立或 `loop` 语义不匹配，
  再退回「改 `next_tame` + SF」。scouting 车道的第一问应是这条 bridge 是否成立。

## 2. W2 — CertShards：成本均衡合并（第二优先，需改验收口径）

- **发现**：合并在时间上几乎免费（同批根 4→1 文件墙钟下降、RSS 不变）；RSS 与
  range 长度/工作量无关，单文件墙钟才是约束。合并的价值不在时间，而在**公理数**。
- **形态**：按「单文件墙钟上限 T」反算最少 shard 数；无上限时全库 3 条 + 5 Tri。
- **裁决点**：与 AGENTS §1「恰好 585 条」冲突 ⇒ **必须用户改裁**；需把 `range'`
  coverage 检查推广成索引列表并集检查（组合检查，秒级）。失去分片级断点续跑，
  单文件墙钟以小时计。

## 3. W3 — Interval：cases-swap P3-GO 批（第三优先，需批产；当前未批缓行）

- **现状**：cases-swap P0/P1/P2/C840 已落库；P3 五族的规格与逐族精确 Bernstein min
  已在 `cases-swap-prep-w1/PREP.md` §3，**尚未批产**（不是「已在飞」）。
- **目标**：按 P3-GO 批把剩余 5 族换装为 Bernstein 单叶 + 桥；规格里的精确 min
  已用 Fraction 验证，桥复用既有 `evalReal` 恒等式，不改信任面。
- **约束**：CertD/CertP 单文件 11–22 GB，只能单槽独占；发射 ~10–20 min/案。
- **裁决点**：用户批产后再开生产车道；先做 C2125338128M（优先、精确 min 已验）。

## 4. W4 — Interval：通用 Bernstein 非负定理（期权，真证明工作）

- 目标：把「每叶 22 行/系数」的 peel 塔换成一条通用定理 + 系数向量数据 + 反射引理，
  可能把 `C2485876245b`（现发射面 NO-GO）翻案。
- 成本：2–3 车道日；风险：反射引理的 `decide` 大整数系数比较可能过慢，
  禁止退回 `native_decide`。
- 状态：期权，不排进近期。

## 5. 不要再试（机器证据，2026-11-21 新增）

| 路线 | 证据 | 结论 |
|---|---|---|
| CertShards 跨根记忆化 / 根覆盖 | 12 根、538,669 节点、两两交集 0 [exact] | 闭包是不相交森林 |
| CertShards 根内去重 | Pent 重根 dup_ratio = 0 [exact] | 无重复 pop |
| CertShards 死根剪枝（343 Pent） | 每根 1 pop，全删约省 100 s | 收益 ~0.03%，不值得 |
| Interval 叶级去重 / 对称合并 | 最大剩余 bank 4.6 万叶、0 重复 box [exact] | 满二叉、互不重叠 |
| 靠重分片省「总编译时间」 | 只省每文件固定开销，工作量可加 | 时间只能靠 W1/W3 |

## 6. 口径提醒

- **585 是公理数** = 580 CertShards 文件 + 5 Tri；`GoodListShard` 199 文件是
  **零公理**的另一套枚举，不要混算。
- **CertShards 峰值 RSS ≈ 1.6 GB**（数据 olean 导入地板，枚举只加 ~0.13 GB）；
  **12.6 GB 属 `Graphs/TopReplay*Shard*`**，不是 CertShards。
- Interval 的 20 GB oleans / 967,759 叶是 **baseline R** 口径；当前树已换装
  4 个 case，引用前先扣已兑现部分。
- ArchiveData/CertData 的 olean 膨胀 36–106×，是 1.6 GB 地板的来源；紧凑表示
  收益主要是磁盘/导入时间，改它要重钉 manifest 的 6 条数据源哈希（P3）。

## 7. 判词与复现

- 判词：**GO（条件式）**——候选有实测/严格估计的容量下降 + 明确证明义务；
  W1/W2 需要用户改裁，W3 需要批产，W4 期权。
- 复现：快照 `REPORT.md` §6 的 `prototype/` 命令（`case_stats.py` / `inventory.py` /
  `root_overlap.py` / `reshard/run.sh`）；`data/recovery_timings.tsv` 是 694 条
  池恢复日志的解析结果。
- 诚实账：Hex 290 shard 无计时（UNRESOLVED）；CertShards 总工作量只有 192/580
  实测下界；受控重分片实验在 2–3 路并发下测得，绝对值偏高；原始编译日志未随
  快照保存，重分片数字待编排者在空闲窗口复跑。

# Heavy-compute scout（重计算探路）

> **本文件是重计算条目状态的唯一维护处**（用户 2026-11-10 指令）。所有“重计算”
> 条目的清单、实测、外推、最佳实践、止损与结论都记在这里；`docs/priority-queue.md`
> §8 只引用本文件，不再重复数字。
> 状态：**活跃**（2026-11-10 12:20 起）。机器：Apple M3 Pro / 12 核 / 36 GB /
> darwin 27.0.0（当前本机）。

## 0. 红线（先于一切）

- **全量** 580 条枚举 shard 拉内核重放 = `AGENTS.md` §1 明确不做
  （既有实测判词：4,450–6,550 核时 + 内存不可行）。本文件里的 A 只做**小样本标定**，
  不是全量重放，也不产出任何“改信任基座”的动作。
- 不做：证书农场、`lake build`、新增 `native_decide`、LP 重建/解冻、D 证书层、
  certtm TM3/Mono*。
- 本文件的运行一律是**测量**：探针文件临时（`lean/heavy_scout_tmp.lean`，跑完删）、
  产物写 `/tmp/heavy_scout/`、不新增公理、不改库。
- 并发 ≤3 个 lean；单 root 一进程；`nice -n 19`。

## 1. 已完成、**不要重做**的（用户 2026-11-10 问“是不是以前做完了”的答案）

| 事项 | 状态 | 证据 |
|---|---|---|
| 信任基座本体（585 条 shard，`native_decide`） | **已完成**（2026-08/09） | `docs/trust-base.tsv`（585 条 manifest，可 replay） |
| 23 条 axiom → kernel `decide`（非枚举那半边） | **已完成**（2026-11-06） | `5ed1bb16`/`f686ca1a`/`2ef062e8`，公理面 −23 |
| **Tri 类纯内核 `decide` 交叉校验**（312k 节点） | **已完成**（≈26 核时） | `docs/architecture.md:94` |
| 549 家族证书生产（50 shards × 20 leaves） | **已完成**（旧机） | `pipeline/interval/out/prod549/val1000/build_stats.json`：main 1022.8 s / 11.2 GB per shard；native 控制 208.2 s / 6.6 GB |
| LP pilot 端到端 | **已完成**（旧机） | `pipeline/lp/PILOTCM_PERF_NOTES.md`：~650 s/单核 per LP |

**未做过的只有一件：580 条枚举 shard 的“纯内核重放”全量**（被 §1 判为不做），
以及它的**本机标定与内存模型**。A 就是后者的小样本，不是重算证书。

## 2. 条目清单（A–E）

| 条目 | 规模 | 已知成本 | 状态 |
|---|---|---|---|
| **A. 信任基座 shard 内核重放采样** | 16,530 roots / 585 shards（Pent 7063、Hex 6584、Quad 1183、HexR 1095、QuadR 400、PentR 160、PentR2 30、PentR3 10、HexR2 5） | 见 §4（本机实测中） | **进行中（用户 2026-11-10 批准）** |
| **B. 549 一个 shard 重放** | `C549ProdS0001`（20 leaves） | 旧机 1022.8 s / 11.2 GB | **排队**（等 A/W41 让内存；用户已批准） |
| C. LP 端到端 | 1 LP（pilot） | 旧机 ~650 s/核 | **冻结，不跑** |
| D. BIEFJHU 72 盒 C 路径 | 72 boxes | fill 135 s/box（本机实测，W41 在飞） | W41 在飞，不另起 |
| E. dReal/Arb 非线性 | — | 未知 | 本机 `pipeline/tools/` 不在（旧机才有），不启动 |

## 3. A 的方法（可复现）

- 生成单 root 探针（`/tmp/heavy_scout/run_root.py`）：
  ```lean
  import Kepler.Graphs.CertCheck
  import Kepler.Graphs.CertData.<Data>Top
  import Kepler.Graphs.Worklist
  namespace Kepler.Graphs
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  example : (List.range' <start> 1).all (fun j =>
      decide (loop (next_tame <p>) (checkFinal (buildBuckets <Data>Data)) <fuel>
        [<Data>Frontier[j]!] = some true)) = true := by decide
  end Kepler.Graphs
  ```
  = 把对应 shard 的 `native_decide` 换成内核 `by decide`，只取该 shard 的第一个 root。
- 编译：`cd lean && export LEAN_PATH="$(lake env printenv LEAN_PATH)" && /usr/bin/time -l nice -n 19 lake env lean -o /tmp/... <probe>`。
- 内存监控：`ps -axo pgid=,rss=` 每 5 s 采样进程组总和；
  止损 = 30 min 或 14 GB（本机 36 GB，W41 三路 fill 占 ~16 GB）。
- 结果：`/tmp/heavy_scout/results.tsv`（tag, data, start, p, fuel, wall_s, maxrss_gb, err_gb, status）。

## 4. 结果（滚动）

### A（本机，M3 Pro）

| root | data | p | fuel | wall | 峰值 RSS | 状态 |
|---|---|---|---|---|---|---|
| Quad K003 root 300 | Quad | 1 | 4M | 140.6 s | **8.11 GB**（8 GB 止损） | KILLED:rss>8GB |
| Quad K003 root 300（重跑，14 GB 上限） | Quad | 1 | 4M | 381.6 s | **14.02 GB**（14 GB 止损） | KILLED:rss>14GB |

**A 扫描决定：在此止损，不再跑其余 root**（2026-11-10 12:42）。理由：
最便宜的类（Quad，p=1，fuel 仅 4M）的单 root 在 6.4 min 内就突破 14 GB，
内存增长 ≈37 MB/s 单调上升、无收敛迹象；结论（内存墙）已不可被更多样本推翻，
继续跑只会占用与 W41 争抢的 16–20 GB 内存。**A 的定位回顾：样本标定，不是全量重放**
（全量重放 = AGENTS §1 明确不做）。

### B（549）

（未跑；等 W41 fill 结束后启动）

## 5. 结论 / 外推（滚动）

- **2026-11-10 第一个数据点**：最便宜的 Quad（p=1、fuel 4M）单 root 在 140 s 内
  冲到 **8.1 GB RSS**（≈70 MB/s 增长，单调上升）——内核 `decide` 的 worklist 闭包
  是内存主导，不是时间主导。微探针（`next_tame` 单步）仅 2.75 s / 1.7 GB。
  ⇒ **“内存不可行”的判词在单 root 尺度上被量化复现**：585 shard × 每 root 8 GB+
  的农场在 36 GB 本机上最多 2–3 路并发；全量重放不只是 4,450–6,550 核时的问题，
  还有**内存墙**。
- **第二个数据点（14 GB 上限重跑）**：同一 root 在 381.6 s 时到 14.02 GB 被止损，
  增长 ≈37 MB/s；即使把上限抬到 14 GB 也不收敛。⇒ 单 root 的可行内存需求
  **>14 GB**（进一步抬上限在 36 GB 本机上会与 W41/系统争抢，超出现有实验窗口；
  记为下界，不再实测）。旧机 128 核 / 503 GB 的“内存不可行”判词在本机更强。
- 与旧机对照：旧机 128 核 / 503 GB 时判“内存不可行”；本机 36 GB 只有更紧。

## 6. 最佳实践（滚动）

1. 单 root 一进程（同一进程内连续跑多个 root 会叠加内存/求值历史，测量失真）。
2. 内核重放必须显式 `set_option maxHeartbeats 0` 与
   `maxRecDepth 100000`；否则默认递归深度先炸。
3. 用 `ps -axo pgid=,rss=` 抽样做止损，不要等 `/usr/bin/time -l`（只在进程退出时输出，
   被止损杀掉时拿不到）。
4. 探针文件放 `lean/` 根（island 编译要求），跑完立即删；结果与日志放 `/tmp`。
5. 与 W41 的 fill 进程共存时，内存预算按“W41 16 GB + 本测量 ≤14 GB”分配。

## 7. 下一步

1. ~~等 A 首个 root 的 14 GB 重跑结果~~ **已完成（见 §4/§5），A 止损**；
   A 的最终结论 = 单 root >14 GB 内存墙，全量重放维持不做。
2. W41 fill 结束后跑 B（549 shard 重放，旧机 1022.8 s / 11.2 GB），得“旧机↔本机”换算因子。
3. 结论稳定后，把本文件 §5 的数字抄进 `docs/priority-queue.md` §8 续条（只引用，不重复维护）。

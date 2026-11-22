# CertShards 同语义代码写法调研（`certshard-code-shape-w1`）

> 状态：研究收线 **GO（条件式）**；只做研究/小原型，**不落库**、不改 585 公理面。
> 证据快照 `~/c17_backup/lane_snapshots/certshard-code-shape-w1/`（175 件
> `MANIFEST.sha256` 全 OK、0 symlink）；`DELIVERY.md` / `REPORT.md` /
> `data/measurements.csv` / `prototype/` / `logs/`。主仓 tracked 零改动。
> 编排者独立复跑 median Pent（§4），数字与车道一致。

## 0. 一句话

580 个 CertShards 重片的时间**几乎全在 `native_decide` 的 IR 解释器**（profile
~99.9%）；23 行的 shard 文件只是调用。三条**同语义**代码写法 **C1+C2+C3**
在 Pent/Quad 实测 **1.20–1.24×**；HexR 含 C4 为 **1.30×**。全部是 DEF-FIX
（改 def body、同名同陈述、附等价证明），不增/不减/不改 585 条
`native_decide` 公理。

## 1. 基线：重片确实是总量大头

- 192/580 有计时（`recovery_timings.tsv`）：合计 **32.49 h**；中位 **96.27 s**
  （两中值 93.55/98.98 的平均；车道报 93.55 是下中位，98.98 并非
  `Pent/K100` 单值）；p90 nearest-rank **1,476.63 s**（`QuadR/K066`）；max
  **8,137.59 s**（`PentR/K001`）。
- 分族：Pent 142 件 24.41 h（mean 618.9 s）+ PentR 12 件 5.88 h（mean 1,765 s）；
  Quad 3 件 1.01 h（mean 1,214 s）+ QuadR 35 件 1.18 h（mean 121.4 s）。
  Hex 290 / HexR 219 / HexR2 5、PentR2/PentR3 均**无计时（UNRESOLVED）**。
- **Hex 首次计时**：主仓 `.lake` **缺 `Kepler/Graphs/CertData/HexTop.olean`**；
  岛协议单编 **1,072.92 s / 20.71 GB / 295 MB olean**（单进程已近 24 GB 闸）。
  `HexR` root 5 = **2,389.82 s**（39.8 min），`Hex` root 100 = **5.58 s**
  （根间差 ~428×）。[EST] HexR 1,095 根 ≈ 730 h、全基座 ≈ 770 h
  （只测 1 根，方差未测，不是实测）。
- **分片 profile**（`Pent/K100`，101.17 user-s）：import **0.676 s**、
  `interpretation` **105 s**、elaboration/typecheck <5 ms。组件份额：
  枚举 88%、`buildBuckets` 10.6%（每文件一次，编译器已提升出 `fun j` 循环）、
  final 路径 1.4%。枚举内：`subdivFace` 38.8%、`polysizes/squander` 28%
  （其中 `ExcessTable` 占 squander ~85%）、`notame` 15.9%、duplicate-edge
  filter 9.8%、`indexToVertexList` 4.4%、`enum` 1.2%。

## 2. 三条 GO 候选（全部同语义）

| ID | 改法 | 实测 | 同语义证明义务 |
|---|---|---|---|
| **C1** | `ExcessAt`（`Generator.lean:35`）：每顶点 4 遍 `facesAt` + filter → 单趟 `vstatsGo`，遇非 final 面早退 | squander **−30.8%**、`next_tame` **−9.4%**；567 样本 0 mismatch；K100 约 −7–8% | `vstatsGo ↔ finalVertex/tri/quad/except`（~50–100 行）；`ScoreProps.lean` 约 10–30 条引理重写 |
| **C2** | `buildBuckets`（`CertCheck.lean:50/57`）：线性 `insertBucket` O(n²) → 按 key 稳定排序 + 分组 | `buildBuckets PentData` **9.36 → 1.09 s（8.6×）**；QuadData 0.592 → 0.085 s（6.9×）；sorted 表逐 key 相等；K100 −8.2% | `lookup` 逐 key 相等（`mergeSort` stable + group，~150–300 行）；AFP `ArchCompAux.thy` 原版用 Trie 背书 |
| **C3** | `generatePolygonTame`（`Generator.lean:157`）：先剪 `countVertices + added > 15` 的候选 | 11.0% 候选跳过构造；118/118 顶点数公式验证；K100 −3.7% | `subdivFace` count 递推 + `tame10ub` 展开（~100 行）；这些候选本来被 `notame` 丢弃 |

**NO-GO（已实测，不要重试）**：C4 `faceListAt` zip 在 sample 级快，但全 loop
Pent **+0.8%**、p90 **+0.3%**；C5 `splitFace` 融合 **慢 19%**；C6
`@[specialize] loop` 无效果；C7 `tame11b` 单趟融合无效果；C8 `enumTab` 缓存
（枚举仅 1.2%）、C9 紧凑数据表示（import 仅 0.68 s）不做。

## 3. 包结果与 caveats

- `Pent/K100`（50 roots）：baseline 101.17 user-s → C1+C2 **87.72（1.153×）**
  → C1+C2+C3 **81.81（1.237×）**，`native_decide` RC=0。
- p90 级 `QuadR/K071`（floor-p90，1,356.67 user-s）：C1+C2+C3 **1,125.92
  （1.2049×）**；含 C4 1,129.07（1.2016×）。
- `HexR` root 5：2,386.78 → **1,839.07（1.2978×）**，RC=0；**该数含 C4**。
  按 C4 在 Pent/Quad 的中性结果，C1+C2+C3-only 预计 ≥1.298×，但**未单独测**。
- **caveats**：fast 原型是**新旧 defs 并存**的克隆（编译器多编一份，真实
  DEF-FIX 应更快，故表中是保守下界）；等价性是**样本级**（567/118）不是形式
  证明；p90 对照跑的是 floor-p90 `K071`，最近秩 `K066`（1,476.63 s）未跑；
  HexR 只测 1 个根，`~770 h` 是外推；2.6 s 的小分片（`K051`）fast 无净收益
  （固定 import/codegen 主导）。
- 编排者独立复跑 `Pent/K100`：baseline **101.23 user / 102.95 wall / 1.764 GB**；
  fast **82.15 user / 83.77 wall / 1.777 GB** → **1.232×**（与车道 1.237× 一致）。

### 3.1 一个 10 分钟大 shard 的估算

三条改动里，C1/C3 随枚举工作量缩放，**C2 是每文件固定节省**（`buildBuckets`
9.36→1.09 s，PentData；QuadData 0.5 s）。所以不能把 101 s 样本的 1.237× 直接乘到
600 s 上：

`T_new ≈ T_old − (C1+C3 比例 × T_old) − C2_fixed`

| shard 类型 | 实测基线 | 10 min → | 省 |
|---|---|---|---|
| **Pent 型**（K100 口径：C1+C3 约 10%，C2 固定约 8–10 s） | 101.17 → 81.81 s（1.237×） | **约 8.8 min（529 s）** | 约 1.2 min |
| **QuadR 型**（K071：C1+C3 约 17%，C2 固定约 0.5 s） | 1,356.67 → 1,125.92 s（1.205×） | **约 8.3 min（498 s）** | 约 1.7 min |
| **HexR 型**（root 5，含 C4） | 2,386.78 → 1,839.07 s（1.298×） | **约 7.7 min（462 s）** [EST] | 约 2.3 min |

- 若只按 1.237× 粗算，10 min → 8.1 min；但那是 101 s Pent 样本的口径，C2 的固定
  节省被放大。真正的 10 min Pent shard 更接近 **8.8 min**。
- QuadR 的 1.205× 本身来自 1,357 s 长 shard，外推到 10 min 最可靠。
- HexR 的 1.298× 含 C4；C1+C2+C3-only 未单测，按 C4 在 Pent/Quad 中性/略负预计
  ≥1.298×（即 ≤7.7 min），标 [EST]。
- 这些是 CPU/user 比例；wall 在 pressure=1、2 lean 环境下与 user 比例接近
  （K100 102.95/83.77 = 1.229）。并发更高时会抖动。
- 真实 DEF-FIX 可能略快于原型（原型新旧 defs 并存），但等价性证明/模块 olean
  增大有一次性成本；10 min 量级内不改变上述区间。

## 4. 同语义与信任边界

- 所有候选都是 **DEF-FIX**：改 def body，**名字/定理陈述不变**；证明行为等价
  （C1 是 list 归纳；C2 是 `lookup` 逐 key 相等；C3 是 count 递推 + filter 交换）。
- shard 陈述仍是
  `loop (next_tame p) (checkFinal (buildBuckets Data)) fuel [Frontier[j]!] = some true`；
  585 条公理的**名字/数量/类别不变**，不新增 `axiom`/`sorry`/`native_decide`。
- 施工时必须走 `docs/def-fix-charters/`：等价性证明 + 受影响 shard 重编译 +
  编排者亲跑 `#print axioms Kepler.the_kepler_conjecture_e2e`（标准三 ∪ 585）。
- 最大工程量不是数学，是 `Kepler/Graphs/ScoreProps.lean` 中展开
  `ExcessAt`/`ExcessTable`/`buildBuckets` 的引理重写（估 10–30 条）。

## 5. 下一步（未批，未开工）

0. **执行模式已实测 GO（有界，2026-11-22 `precompile-shard-probe-w1`）**：
   `precompileModules` + `--load-dynlib` 在真实 QuadR 上 **K068 12.9× / K071 13.8×**
   （编排者复跑 K068 13.2×），一次性 ~100 s / 5.45 GB / dylib 7 MB；详见
   [`compile-speed.md`](compile-speed.md) §3.2。**尚未 production 化**（三件探针手段
   待消除）。native 后 C1/C3 省的是解释执行工作量，边际比例缩小；C2 的
   `buildBuckets` 固定费在 native 下也已 <0.1 s，绝对收益变小。**建议先做执行模式，
   再重估 C1+C2+C3；两者不冲突，但不要按原比例叠加。**
1. **C1+C3 施工**（证明面小）：预计 Pent 类 −11–12%，先验证 DEF-FIX 流程。
2. **C2 施工**（证明面中等）：固定费 −8.3 s/文件，对 1-root/5-root 小分片绝对收益
   最大。
3. C4 已 NO-GO，不并入；C5–C9 不做。
4. 施工范围仅限代表性 shard 重编译 + 等价性证明，不重跑全 585；全基座 replay
   仍等池恢复（HexTop olean 也缺）。

## 6. 复现

```bash
SNAP=~/c17_backup/lane_snapshots/certshard-code-shape-w1
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$(cat $SNAP/data/lean_path_main.txt)"
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
/usr/bin/time -l nice -n 19 lean -o /tmp/base_K100.olean \
  Kepler/Graphs/CertShards/Pent/K100.lean
# fast 原型（新 defs + 旧 defs 并存；保守下界）
mkdir -p /tmp/csroot && cp $SNAP/prototype/probe_combined2_K100.lean /tmp/csroot/
/usr/bin/time -l nice -n 19 lean -R /tmp/csroot -o /tmp/fast_K100.olean \
  /tmp/csroot/probe_combined2_K100.lean
```

Hex 首测：`$SNAP/prototype/hex_repro.sh`（需先按脚本建 island，补
`HexTop.olean`，~1,073 s / 20.7 GB）。复测前过 guard：`lean ≤3 ∧ 总 RSS ≤24 GB
∧ pressure <2`；单 lean、`nice -n 19`。

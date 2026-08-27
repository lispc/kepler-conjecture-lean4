# PilotCM204880136538 — 列主序试点性能记录（2026-08-27 实测）

本机 128 核 / 503G，单核很慢（native_decide ~360 pops/s）。所有数字为
`lake build` / `lake env lean` 单核 wall/user 实测。

## 目标与基线

- 行主序单块 `decide`：25304 s（历史）
- 行主序逐列分片 96 并发端到端：1542 s（历史）
- 目标（历史推断）：~30 s/LP（基于"O(nnz) 即可达 30s"的假设）

## 实测（真实图 204880136538：915 变量 × 3882 行 × 8056 非零，Y ~900 位）

| 阶段 | 树索引版 (checkDualCMTBase) | flat 锁步版 (checkDualCMTBaseFlat) |
|---|---|---|
| Data 字面量阐明（cs/b/certY 分块 def + `: ColI` 标注） | 423 s | 423 s |
| `base_check` decide（含 bᵀY ≤ G） | ~113 s（768-655） | **~49 s**（472-423） |
| `cols_check` decide（单 O(nnz) 树 decide） | ~190 s | ~169 s（ColsOnly 实测 3m18 user，含 import） |
| 端到端单核（Data + Assembly） | ~990 s | **~650 s** |

相对基线：单核 ~650 s ≈ 行主序单块 25304 s 的 **~39×**、96 并发分片端到端
1542 s 的 **~2.4×**（且本实现是单核！）。base/cols 两个 decide 独立，可双核并行。

## 瓶颈定位

1. **`bDotTP` 二次方索引**（已修复）：`s+1` 构建一元 `Nat.succ` 链，`getF`
   逐级比较 O(s)，整个 bᵀY 变 O(n²)。锁步 `dotLI`（O(n)）修复：
   `dotLI lp.b certY` 3882 项实测 ~42 s，几乎无索引开销。
2. **大整数归约是 cols 主成本**：`dotLI`（3882 项 ~900 位乘）≈ 42 s，
   每项 ~11 ms；`cols_check`（8056 项）≈ 169 s 与之成 nnz 比。
   gcd(Y,D)=1 不可缩放；乘数位宽（b 侧 1 位 vs 50 位）不影响，成本由
   ~900 位 Y 侧主导。
3. **字面量阐明 423 s** 是每 LP 固定成本（同行主序量级，且 `: ColI`
   标注避免 ~30 列处 pending-MVar 超线性爆炸——未标注时实测 >500 s）。

## 结论（诚实）

目标 ~30 s/LP **不可达**：内核 `decide` 重放 ~12k 次 ~900 位乘，本机单核
~11 ms/项 ⇒ 纯算术下限 ~130 s，加字面量阐明 ~420 s ⇒ ~550-650 s/LP 单核。
可行取舍：单 LP 单核 ~11 min；Data/cols 双 decide 并行 ~7-8 min；仍优于
行主序分片基线（26 min 96 并发）。进一步优化需减小证书整数字宽（求解侧
取更小分母证书）或换 checker 语言（native_decide 被红线禁止）。

## 复现

```sh
cd pipeline/lp
python3 socert.py pilot/pilot_204880136538_flat.lp --col-major \
  --module PilotCM204880136538 --terminal-bound 12
cd ../../lean
lake build Kepler.LP.PilotCM204880136538.Data      # 472 s（含 flat base_check）
lake build Kepler.LP.PilotCM204880136538.Assembly  # 222 s（含 cols_check）
lake env lean Kepler/LP/PilotCM204880136538/Bench.lean  # 单文件基准
```

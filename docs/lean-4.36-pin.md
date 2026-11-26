# Lean 4.36 升级 pin（可复现依赖集合）

> 状态：**候选 pin，未切换**。主仓 `lean/lean-toolchain` 仍为 `v4.32.2`。
> 本页固化 4.36 兼容车道实际使用的工具链与依赖 rev，作为阶段 4（切换）的
> 唯一依赖集合；切换时**不得浮动升级**。
> 证据源：`~/c17_backup/lane_snapshots/lean436-pilot-w1/`（`lake-update.log`、
> `toolchain-version.txt`、`toolchain-install.log`）与 `lean436-blockers-w1` 的
> 4.36 直编日志（2026-11-26）。

## 1. 工具链

| 项 | 值 |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.36.0` |
| Lean commit | `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| 平台 | `arm64-apple-darwin24.6.0`，Release |
| elan 安装路径 | `~/.elan/toolchains/leanprover--lean4---v4.36.0/`（约 3.0 GB） |
| 版本核验 | `Mathlib.olean` 头 `olean / 4.36.0 / 611c117b…`（2026-11-26 复验） |

## 2. 依赖 rev（`lake update` 解析结果，pilot `lake-update.log`）

| 包 | rev |
|---|---|
| mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`（tag `v4.36.0`） |
| batteries | `b4b25a3886a16daacaf6615c2eea7170a6e8f458` |
| aesop | `66ff77cf0c4c898799e4b94d14db55f7a02d0c5a` |
| Qq | `ff055a2fcc835935e0ae607339b455a5f5896b4b` |
| plausible | `054b228ce0ac61d767c6e71ba73a24728f191b72` |
| importGraph | `8370c640afcd1cc3fb1cb9bf1560cc66eafee5e0` |
| LeanSearchClient | `4fb58e749ef3fc0395fe274f6cab70c2ea85f1c9` |
| proofwidgets | `2f0f3520daeac2d9310ff25b7a877a0e5cdaa203` |
| Cli | `50810f72af7618bee62fe9800dc26e806c188703` |

Mathlib cache：9,117 文件预构建（`lake update` post-update hook 自动 `cache get`），
4.36 侧 **零本地 Mathlib 编译**。

## 3. 使用方式（兼容期，主仓不切）

- 直编：`~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean -M <MB> -j 1 -o <岛>/<Mod>.olean <源>`
  + `LEAN_PATH` 指向 4.36 依赖 olean 池 + 已编译的 Kepler olean 池。
- 岛必须是**复制式**（`cp`/`rsync`），禁 symlink；主仓 `.lake` 只读（PR-36/9）。
- 并发护栏：lean ≤3 ∧ 总 RSS ≤24 GB ∧ pressure <2（AGENTS §4）。
- 重件预算：`ArchiveData.Pent` ≥24 GB（4.36 实测峰值 20.57 GB）、
  `CertData.PentTop` 15.48 GB / 1164 s、`PackingAuto21` 16.33 GB、
  `ZTGJoint0000CornersP` 21.25 GB —— 单槽独占，`-M` 杀进程记“单槽重跑”而非 block。

## 4. 切换（阶段 4）检查单

1. `lean-toolchain` 改为本页 §1；`lakefile.toml` mathlib rev 改 `v4.36.0`；
2. `lake-manifest.json` 使用本页 §2 的全套 rev（禁止 `lake update` 浮动）；
3. 新复制式岛做依赖解析 + cache 恢复，主仓 `.lake` 不共享；
4. 按 MIGRATION 阶段 4 顺序恢复：cache → 基础模块 → CFW/CertD/Nli 代表链 →
   K009/GoodList → 585/Final；
5. 任一失败即停，不用后续缓存掩盖；回滚按 MIGRATION 的逆序执行。

## 5. 已知未决（切换前必须闭环）

- `Text.Planarity`：`azim_cone_of_combo` 在 4.36 @5M heartbeats 超时
  （20M 诊断通过，253 s/245 s）；需拆分证明，不得以调 heartbeats 代替。
- `PackingAuto8:295`：`VSub ?m (Set V3)` synthInstance 失败（未修）。
- GoodList `+Classical.choice` 证明级漂移（根面不变，但破坏 good_list 零公理叙述；
  待定位或记 ERRATA）。
- `Assembly.lean:3693/3707/3722`、`PackingAuto14` 等 `Equiv.ofBijective_apply`
  同模式点（全树 80 处/23 文件，以 4.36 census 实测为准）。
- 全量 4.36 census（Final 闭包）与 585 逐名公理复核尚未执行。

# DEF-FIX 章程：SF-99 `Deformation` 开区间纠正（2026-11-05，编排者拟；用户同日批准）

> 依据：`docs/statement-fix-proposals.md` §99 + PROPOSAL-99-AMEND（`sf99-scout-w1`
> 全库 79 个声明级站点测绘）。用户裁决：**走 (a) 根修定义**（不是 (b) 局部补 `ha/hb`）。
> 闸模式 = `GATE_MODE=DEF-FIX`，`DF_PATCH=` 本目录 `gate-<file>.md`（每个被改文件一份，
> 闸门一次只核对一个 `$FILE` 的围栏）。

## 0. 一句话

Lean `Deformation` 用闭区间 `Icc a b`，HOL `real_interval (a,b)` 是开区间
（`a < 0 < b`）；闭区间版允许 `a = 0`，负半窗完全不受约束，使 LA37
`MHAEYJN` 两件与 LA14 `zlz_azim` 的冻结陈述**为假**。本修把两个定义根
（`Deformation` / `deformation_p2`）与两个窗口适配点改成 `Ioo`，`zlz_azim`
一行转调已证的严格形。

## 1. 对象与 HOL 锚

- HOL 定义：`reference/flyspeck/text_formalization/local/localization.hl:128`
  （`(&0) IN real_interval (a,b)`，第二合取在 `real_interval (a,b)` 上给
  `continuous atreal`，第三合取 `ff v (&0) = v`，止于 `localization.hl:131`）。
- Lean 冻结定义：`lean/Kepler/Text/LocalAuto1.lean:129` `Deformation`；
  独立复制体：`lean/Kepler/Text/LocalAuto2.lean:300` `deformation_p2`。
- 语义差：`real_interval (a,b)` ↔ `Set.Ioo a b`；旧编码 `Set.Icc a b` 只给
  `a ≤ 0 ≤ b`，新编码给 `a < 0 < b`（`0` 永远是内点）。端点连续性无消费者
  （`sf99-scout-w1` 实测 `c` 类 = 0）。

## 2. 改动范围（5 个声明 / 12 行；净 sorry = −1）

| 文件 | 声明 | 改行 | 性质 |
|---|---|---|---|
| `LocalAuto1.lean` | `Deformation` | 1 | ROOT：`Icc` → `Ioo`（两处） |
| `LocalAuto2.lean` | `deformation_p2` | 3 | TWIN-ROOT：同一 patch，防语义分裂 |
| `LocalAuto21.lean` | `deformation_restrict_p21` | 1 | k1 适配：`0 ≤ e` 从 `le_of_lt` 取 |
| `LocalAuto34.lean` | `DEFORMATION_SMALL_INTERVAL_p34` | 2 | k1 适配：首合取与成员严格化 |
| `LocalAuto14.lean` | `zlz_azim_p14` | 1 | PROOF-FIX：转调 `w9_zlz_azim_strict` |

- 不改任何陈述（statement 行逐字未动）；`_discharged` 线、capstone 元组、
  `MHAEYJN_prop_p37` 等 6 份 Prop 孪生**零改动**随定义自动转真。
- 不把 `_hpin`/`_haff`/`h4` 的 `Icc` 改成 `Ioo`（那是「Lean 假设更强 ⇒ 定理更弱
  但为真」的方向，单独立项）。

## 3. 破坏面与验收

- 13 文件依赖序：LA1 → LA2 → LA17 → LA14 → LA18 → LA21 → LA23 → LA28 → LA31
  → LA34 → LA37 → LocalBridge → LocalConcl（LA6 与 LA17 同层一并过）。
- W2 抽检：`#print Deformation` / `#print deformation_p2` 三处 `Ioo`；
  `(a,b)=(0,1)` 对 `MHAEYJN_prop_p37` 不再可实例化。
- 回退：本 patch 整体 `git revert` 一个 commit。
- 风险：全树重编可能暴露测绘外的隐藏站点；LA37 两件陈述恢复真值后，证明缺口
  仍在（G1/G3/G4，另立项）。

## 4. 逐文件闸门

```sh
cd lean
GATE_MODE=DEF-FIX DF_PATCH=docs/def-fix-charters/sf99/gate-LocalAuto1.md \
  DF_ANCHORS="localization.hl:128 localization.hl:131" \
  DF_NAMES="Deformation" DF_SORRY_NET=0 \
  bash scripts/auto_gate.sh Kepler/Text/LocalAuto1.lean Deformation
# 其余四件同理，见各 gate-*.md 的 §2.2
```
（`DF_PATCH` 按仓库根解析；`auto_gate.sh` 内部会补 `$REPO_ROOT/`。）

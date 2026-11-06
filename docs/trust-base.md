# 信任基座 — 与 Flyspeck/Isabelle 的逐类对照

> 口径：**用户 2026-11-06 裁决** —— 终局是「不比 Flyspeck/Isabelle 更差」，不是完美标准三。
> 已写入 `AGENTS.md` §1（验收式）。本文件是那份验收式的**依据与现状**。
> 数字只引用不抄：基线以 `docs/priority-queue.md` 文件头为准。

---

## 1. 验收式（AGENTS.md §1 原文）

```
#print axioms Kepler.the_kepler_conjecture_e2e
= [propext, Classical.choice, Quot.sound] ∪ {约 585 条地面 native_decide 公理}
```

外加三条：

1. **零 `sorryAx`**；
2. 每条公理的陈述是**封闭可判定的地面事实**，进 manifest、可 replay、注明数据源与生成器版本；
3. 与原文形式化的 `same*`/`pre_iso_test*` **同数据、同信任类别**。

**唯一还算"债"的是 `sorryAx`。** 621 条公理是**声明的信任基座**，不是债。

---

## 2. 逐类对照（证据都在 `reference/`）

| 信任类别 | HOL Light Flyspeck | Isabelle AFP | 我们 | 判定 |
|---|---|---|---|---|
| 内核 | LCF kernel（`fusion.ml`） | Isabelle LCF kernel | Lean 4 kernel | **对等** |
| 区间算术 / LP 证书 | **形式化验证**（Solovyev `formal_ineqs/`、`formal_lp/`） | — | 内核 `IExpr`/`checkPos` 重放 | **对等** |
| `good_list` 归档校验 | **零公理真证**：`tame/good_list_archive.hl` 的 `all_conv_univ (eval_good_list0 …)`（`eval_good_list0` 见 `formal_lp/hypermap/computations/list_hypermap_computations.hl:449-468`） | `pre_iso_test3..6`，`by eval` | 23 条 `native_decide`（**已改 3 条为 kernel `decide`**） | **原为我们的退步 → 正在追平** |
| tame 枚举 | **明写跳过**（`tame/tame_concl.hl:26`：`(* WTEMDTA_concl skipped … *)`） | `same3..6`，`by eval`（`Computation/ArchComp.thy`，35 行 8 条；session `(slow very_slow)`、`timeout = 50400`） | 585 条 `native_decide`（580 `*_shard_*` + 5 `tri_shard_*`） | **对等**（同类别、同数据；我们分片更细，但分解经机器验证无损，见 §3） |
| `Prop := sorry` 型定义 | 无 | 无 | 1 条（`ox3q1hP25`，`PackingAuto25:90`） | **我们更差 → 必须修** |
| `else True` 回落 / 索引盲谓词 / 空量化注册表 | 无 | 无 | `idsLpIneqs := []`、`LpTerminalCertified(_id)`、`certifiedIneqHolds_pilot` | **我们更差 → 必须修** |

`by eval` 是 Isabelle 的 code generator 求值 ⇒ **它才是 `native_decide` 的对应物**。
所以「624 变标准三」是**比原版更高的要求**，不是补原版做过的事。

---

## 3. manifest 与无损分解

生成器：`scripts/trust_manifest.py`（从 `docs/e2e-reachability-map.tsv` 的 `--- AXIOMS ---`
段取名单，逐条 `#print` 取陈述，校验后写 `docs/trust-base.tsv`）。

```sh
python3 scripts/trust_manifest.py           # 生成 manifest
python3 scripts/trust_manifest.py --check   # 只校验（CI 用）
```

它校验两件机器可判的事：

**(a) 地面性**：每条陈述必须是 `decide (<闭项 Bool>) = true`，不出现 `∀`/`∃`/自由变量。
**基线 R 实测：621 / 621 通过，0 条非地面，0 条形状未知。**

**(b) 分解无损**：`*_shard_*` 的 `List.range' a l` 区间在每个 `(类, next_tame p)` 上
**无空隙、无重叠**地铺满 `[0, max(a+l))`。铺满 ⇒ 580 条分片合起来**就是**一条 ∀ 事实，
即 Isabelle 的 `same3..6` 那一条。**这是"不比他们差"最硬的一句证明**，且是组合检查（秒级），
不是重算。

基线 R 实测（全绿）：

| 类 | `next_tame p` | 片数 | 覆盖 | 空隙 | 重叠 |
|---|---|---:|---|---:|---|
| Hex（含 HexR / HexR2） | 3 | 290 | `[0, 7684)` | **0** | **0** |
| Pent（含 PentR / PentR2 / PentR3） | 2 | 198 | `[0, 7263)` | **0** | **0** |
| Quad（含 QuadR） | 1 | 92 | `[0, 1583)` | **0** | **0** |
| Tri | 0 | 5 | 单种子（`tri_shard_i`，fuel 500000） | — | — |

另有一档同类的无损分解：`good_list` 归档切片（`List.take N` / `List.drop M`）——
Hex 3 片、Pent 17 片，**逐片首尾相接、从 0 起**（末片 `List.drop` 到尾）。
（Quad/Tri 的 20 片已由 `5ed1bb16` 改成 kernel `decide`，不再是公理。）

7 种形状的分布（基线 R）：`shard-range` 580 · `goodlist-slice` 20 · `tri-single-seed` 5 ·
`archive-pre` 4 · `top-no-finals` 4 · `top-bounds` 4 · `top-replay` 4。

---

## 4. 残余风险（诚实清单）

1. **`native_decide` 信任 Lean 编译器 + 运行时 + `Decidable` 实例的正确性。**
   Isabelle 的 `by eval` 是从**已证方程**生成代码，伪造不出实例；我们这边理论上可以写一个
   `Decidable` 实例让它证出假命题。**这是唯一一处我们严格弱于 Isabelle 的地方。**
   缓解（**待做**）：审计公理依赖闭包里的 `implemented_by` / `@[extern]` / `unsafe` /
   手写 `Decidable`，确认全部是派生实例。检测器：
   `grep -rn 'implemented_by\|@\[extern\]' lean/Kepler/`。
2. **数据来源一致性（待做）**：我们的 `ArchiveData/{Tri,Quad,Pent,Hex}` 是否与 HOL
   `tame_list.hl` / Isabelle `Archives/*.thy` 同一份数据。若一致，§2 第 4 行从"我们自己的
   事实"升级为"和他们同一个事实"。
3. **生成器版本**：manifest 目前只钉公理名 + 陈述哈希，还没有钉数据源哈希与
   `gen_goodlist_shards.py` 的版本。待补。

---

## 5. 明确不做（AGENTS.md §1 已写）

- 580 条枚举 shard 拉进内核重放（实测 4,450–6,550 核时 + 内存不可行）；
- 证书农场（`cert-cost-scout` 判：树不收敛，不是每叶多贵）；
- 追「真·标准三」。

## 6. 仍然是真活的部分

- **锥内 79 条 `sorry`**（`docs/e2e-reachability-map.tsv` 的 `--- SORRIED ---` 段）。
- `Prop := sorry` / `else True` / 索引盲 / 空量化四类自造缺陷。

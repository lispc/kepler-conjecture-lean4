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

### 2.1 一条对我们有利、但要如实说的细节

HOL Light 的**构建本身是严格的**：`text_formalization/build/strictbuild.hl:111-112`
把 `new_axiom` 与 `mk_thm` 都改成 `failwith`（`"new_axiom has been disabled."`）。
`trig2.hl:723/1014` 里那两处 `new_axiom`（`acs_atn2` / `COS_MONO_LT_EQ`）**都在注释块 `(* *)` 里**，
是后来被真证掉后留下的历史痕迹。

⇒ 逐**单个证明助手**看：HOL 的终定理零公理，我们是 621 条 —— 这一项我们确实弱。
⇒ 逐**整个项目**看：他们的 tame 枚举信任在 **Isabelle 的 `by eval`** 里，只是不在 HOL 的公理表上。
我们的 621 条与它**同类**，区别是**我们的看得见**（`#print axioms` 直接列出来），
他们的藏在跨证明助手的 import 里。

**可采纳的做法**：HOL 用 `strictbuild.hl` 机械禁用 `new_axiom`/`mk_thm`。
我们的等价物 = `AGENTS.md` §2「不许新增 axiom」+ `scripts/trust_manifest.py --check`
（后者是可跑的，前者靠纪律）。这条值得在 CI 里也跑起来。

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

---

## 7. 重计算的成本模型（2026-11-06 实测定案：**按代数结构分档**）

| 档 | s/叶 | 依据 |
|---|---:|---|
| **poly / y-空间** | 5.3 / 11.5 / 12.8 / 17.5 / 23.8 **ms** | 4 个 XL case 端到端构建记录：55k 叶 4m50s、205k 叶 59m50s、1.35M 叶 4h47m、1.67M 叶 5h19m（`docs/archive/root/STATUS-2026-10-23.md:199`） |
| **sqrt / atan** | **0.958 s / 1.330 s** | 编排者重编 `CQITNPEAx3725403817/Shard1254`（**513 叶 / 682 s / rc=0**）与 `Shard1826`（**451 叶 / 432 s / rc=0**） |

**不许再把「1.62 s/叶」当全局常数用。** 它对 sqrt/atan 档是准的（偏保守 25–70%），
对 poly 档高估 **55–300 倍**。根因：按 `ops` 线性外推（`0.0316 + 8.135e-5·ops`）在 sqrt/trans
案例上**结构性失效** —— `ops` 数的是 RPN 节点，而一个 `atan` 结点的原语数是 `N²`
（N=2048 时 4.19M 次乘）—— 一个结点顶 10⁵ 个 `mul`，所以「每叶成本 ∝ ops」不成立。

**规模实测**（基线 R 口径）：`Kepler/Interval/Cases` = 3.8 GB 源 / **10.76M 行** / 17,204 文件 /
**20 GB oleans**；可达结点 2,060,423 = **锥的 98.69%**，其中一个银行
（`CQITNPEAx3725403817`）占 1,853,539（88.8%）/ **967,759 叶**。

**这些证书贡献 0 条公理。** 公理面与计算面几乎不相交：585 个具名声明产出 621 条公理，
2.06M 个证明结点产出 **0** 条 ⇒ **重计算买的是锥，不是信任。**

### 7.1 三个 XL case 是**已付款未接线的资产**，不是浪费

`C3253650737`（1,670,962 叶）/ `C8425800388`（1,346,892）/ `C6078657299`（694,659）：
`docs/archive/lane-archives/mnt11-rolling/M1/CERT-QUEUE.md:158` 明写它们是
**「跨 family 的 XL 规模锚」**，同时（`handoff-2026-10-28.md:728`、`statement-fidelity.md:155`）
是 `kcblrqc_ineq_def` 族的**真证书**。消费点 `Assembly.lean:1955`
`nliKcblrqcIneqDefIds : AllCertified kcblrqcIneqDefIds := sorry`（28 个 id，**锥内**）尚未接线。
它们在图的"可达集"里查不到，只说明**接线没做**，不说明没有用途。

### 7.2 明确不做：把区间证书叶改成 `native_decide`

发射器已支持（`pipeline/interval/emit_lean.py:199` `DECIDE_TAC`、`:3149` `decide_mode="native"`），
建成会快 ~300×，但会凭空造出**约 100 万条 `ofReduceBool` 公理**。Isabelle 整个枚举的信任基座
是 8 条 `by eval` ⇒ **这是"比原版差几百个数量级"，不是"不比它差"**。
新原则只允许**地面事实 + 有界数量**的公理，不授权这一类。

### 7.3 真正的加速在证书格式里

1. **闭常数 Taylor rung**（S，纯发射器）：落库证书头自己写 `N=1024`，当前发射器硬编 2048
   （`emit_lean.py:1297-1298`、`:1102`）。Taylor 项数按 `N²` 计，降到 128 残差已验证 1e-41
   ⇒ 每个 trans 结点少 ~256 倍。`atan(1)` 已有 `pi4D` 快路（`:544`），只剩 `atan(1/√2)`。
2. **Dyadic 表示**（M）：`add`/`ble` 每次都要指数对齐，每个 RPN op 60–108 个 `2^k` 移位步，
   而 `2^k` 在核心里是 **k 步递归乘法**（`Interval/Basic.lean:106,145`）。改成单一固定标度整数
   区间可整块消除，估 2–5×（**EST，未实测**）。

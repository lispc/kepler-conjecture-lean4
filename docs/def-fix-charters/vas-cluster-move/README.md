# DEF-FIX 章程：LA23 VASYYAU 簇下移（`LocalAuto23Vas`）

> **状态：APPROVED（用户 2026-11-13 21:14 批准；V3 执行，待 V2 交付后发车）**。拟案：2026-11-13 编排者（VASYYAU 闸族）。
> 依据：AGENTS §2「定义改动只走 DEF-FIX 通道」+ `docs/def-fix-charters/la-dag-cuts/README.md`
> 先例（用户 2026-11-12 已批裁决 ②a：纯搬运、保陈述逐字节、零 sorry 增减）。
> **批准范围**：§3 的 14 条声明逐字节下移 + §4 的 import 边（新模块汇点）；不含 §4 末的 LocalConcl
> 增 import（留给收口车道）、不含任何陈述/定义体改动。

## 0. 一句话

把 `LocalAuto23.lean` 的 **Section A（VASYYAU/JOTSWIX 簇，:427-646）14 条声明逐字节搬**到新模块
`lean/Kepler/Text/LocalAuto23Vas.lean`（import `LocalAuto1` / `LocalAuto21` / `LocalAuto23` + Mathlib），
donor 删整块（14 条 = 2 条已证 + 12 条 sorry）。**陈述逐字节、sorry 数零增减、零 axiom/native_decide 增删**；
新模块是 import DAG 的**汇点**（无任何现有消费者），静态无环。

## 1. 要解决的问题（R3 DAG 死锁，机器证据）

```
LocalAuto22.lean:94   import Kepler.Text.LocalAuto23      ⇒ LA22 → LA23
LocalAuto21.lean:105  import Kepler.Text.LocalAuto22      ⇒ LA21 → LA22 → LA23
LocalAuto18.lean:108  import Kepler.Text.LocalAuto21      ⇒ LA18 → LA21 → …
LocalAuto25.lean:114  import Kepler.Text.LocalAuto23
LocalAuto16.lean:106/107  import LA22 + LA23
```

VASYYAU 战役的三个硬巨人（`NEHXMWH` / `BZQNDMN` / `JOTSWIX` / `LEMMA_PWE1-4`）在 LA23 体内，
而它们的 HOL 证明要消费 **LA22（`INTERIOR_ANGLE1_AZIM_p22`，V1 `f8adecea` 已真证）** 与
**LA21（`azim_assumption_reduction_p21` / `MMs_minimize_tau_fun_p21` / `WNWSHJT_ALT_p21`，
均标准三）** 的 azim/deform kit。LA23 今天不能 import LA21/22（成环），所以这些件**无法开工**。

## 2. 为什么是「下移簇」而不是「上移 kit」

| 方案 | 动作 | 问题 |
|---|---|---|
| D1（RECON 原案） | 把 LA22/LA5 的 azim kit 上移到新模块，LA23 与 LA22 都 import | 需搬 `LOCAL_FAN_AZIM_POS_p22` 等 + 其私有闭包；LA22 侧要删重复声明 |
| D2 | 再把 LA21 三件上移 | 私有 helper 闭包未核，链更长 |
| **本草案（下移簇）** | 12 条**仍 sorry** 的声明整块搬到新汇点模块 | 无证明体要搬、无闭包问题；搬运面 = 纯文本块 + 1 条 import 边 |

**关键机器事实（2026-11-13 实测，`rg` 全树 `lean/Kepler` 源面）**：
14 条声明在**全树零代码引用**——只在自身定义行、LA23 文件头注释、LA25 注释（:2238/:2249）出现。
⇒ 搬走后无任何模块会 unknown identifier。

## 3. 搬运清单（14 条，全部在 LA23:427-646 连续块内）

| # | 声明 | HOL | 状态 |
|---|---|---|---|
| 1 | `MOD_4_CASES_p23` | JOTSWIX.hl:454 | 已证（`omega`） |
| 2 | `ab4_assumption_reduction_p23` | :476 | sorry |
| 3 | `ab4_assumption_reduction2_p23` | :693 | sorry |
| 4 | `ab4_assumption_reduction_sym_p23` | :900 | sorry |
| 5 | `deform_azim_sum_p23` | :1084 | sorry |
| 6 | `NEHXMWH_p23` | :1171 | sorry |
| 7 | `BZQNDMN_p23` | :1679 | sorry |
| 8 | `JOTSWIX_p23` | :2204 | sorry |
| 9 | `LEMMA_PWE1_p23` | :2706 | sorry |
| 10 | `LEMMA_PWE2_p23` | :2994 | sorry |
| 11 | `LINDIH_11_p23` | :3291 | sorry |
| 12 | `LEMMA_PWE3_p23` | :3370 | sorry |
| 13 | `LEMMA_PWE4_p23` | :3648 | sorry |

（`PERIODIC_INJ_MOD_p23`（:446，已证）同在块内一并搬。合计 14 条 = 2 条已证 + 12 条 sorry。）

## 4. import 边变化

```
新增：LocalAuto23Vas → LocalAuto1, LocalAuto21, LocalAuto23, Mathlib
      （LocalAuto21 → LocalAuto22 → LocalAuto23 已传递，显式导入只为可读性）
删除：无（LA23 的 import 面一字不动；LA22→LA23、LA25→LA23、LA16→LA23 全部保留）
```

- 新模块是 DAG **汇点**：无现有模块 import 它 ⇒ 零环（新增边全部指向上游已有模块）。
- 后续（不在本 patch）：`LocalConcl` 增 `import Kepler.Text.LocalAuto23Vas`，供
  `TUAPYYU_discharged` / `WKZZEEH_discharged` / `PWEIWBZ_discharged` 的收口消费。
- 收益：VASYYAU 簇的证明车道可以直接在 `LocalAuto23Vas.lean` 里 `使用 LA21/22 kit`，
  R3 死锁解除，且不需要替换任何现有声明。

## 5. 不变量（落地闸必须逐条核）

1. **陈述逐字节**：14 条签名行 donor HEAD 文本 vs target patched 文本逐行 EQUAL（脚本比对）。
2. **sorry 零增减**：LA23 块内 12 条 `sorry` + 块外若干不变；全库 `rg -c '^\s*sorry\s*$'` 不变。
3. **零禁项**：diff 全文不含 `axiom` / `admit` / `native_decide`；无新 `sorry`。
4. **import 面**：LA23 import 行零变化；新文件 import 只含上游模块。
5. **无消费者破坏**：`rg` 全树 12 名零代码引用（本草案 §2 证据可复跑）。
6. **根面**：`#print axioms Kepler.the_kepler_conjecture_e2e` md5 仍
   `246e952cde4498a802ca0aabe6842d79`（搬迁不进锥，根面应逐字节同）。

## 6. 落地验证计划（单车道，≤2 lean 并发）

1. worktree@落地 HEAD → 搬块 + 建新文件 → `git apply --check` 反向验证。
2. shadow farm（`la-dag-cuts` 同款硬链接法）：
   - 编 `LocalAuto23Vas.lean`（RC=0 / error 0；预期全 sorry 声明体直接过）；
   - 编 `LocalAuto23.lean`（RC=0；证明删除块后无残留引用）；
   - 编 `LocalAuto25.lean`（LA23 的消费者，RC=0）；
   - 编 `LocalConcl.lean`（若同 patch 加 import；否则不编，闭包声明集不变）。
3. 编排者亲跑根面 md5 + `git apply` 落库一笔 commit。
4. 文档：本 charter 状态改 LANDED + pq §8 一条。

## 7. 风险与回滚

| 风险 | 级别 | 缓解 |
|---|---|---|
| LA23 文件头注释仍把 12 件列为「in-file sorries」 | 低 | 同 patch 改注释（doc-only，不计声明面） |
| 新模块 import 面漏件导致 unknown identifier | 低 | shadow 编译暴露；块内声明只依赖 LA1/2/3/5/9 词汇（`ScsV39`/`Deformation`/`azim`/`dihV` 等） |
| 未来 `LocalConcl` 加 import 时环 | 低 | 新模块只 import 上游；LocalConcl 已是汇点 |
| 语义漂移 | 无 | 纯搬运，零编辑；byte-check 脚本把关 |

## 8. 用户裁决

- [x] **批准本搬运**（用户 2026-11-13 21:14；纯搬运、零陈述改动、零 sorry 增减）→ V3 执行（V2 交付后发车）。
- V3 = shadow 验证（LA23 / LocalAuto23Vas / LA25 / 根面）+ patch + 本 charter 状态更新为 LANDED。

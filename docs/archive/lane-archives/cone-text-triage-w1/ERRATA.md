# ERRATA — cone-text-triage-w1 的 `dep_status` 口径

> 2026-11-06 追加。原 `TRIAGE.tsv` / `RANKED.md` 正文不修改（只增不改），
> 纠正以本文件为准。

## 1. `CLEAN` 的判定错了两次

原口径：`CLEAN = 依赖递归闭包 0 sorry`（grep 声明体）。

**实测推翻**（`la32-4m6-w1`，`#print axioms` 全名探针）：

| 件 | 原判 | 实测 axioms | 原因 |
|---|---|---|---|
| `Kepler.Text.VASYYAU_p25`（LA25:2541） | CLEAN | `[propext, sorryAx, Classical.choice, Quot.sound]` | 它只是 LA1 registry `VASYYAU_concl`(LA1:4913) 的再导出，债在 registry |
| `Kepler.Text.SET_STAB_4M6_ARROW_4T5_p33`（LA33:4298） | 绿前置 | 已证，但 **LA32 不 import LA33**，探针 `unknown identifier` | 跨文件前置不在目标文件 import 闭包内，零新 import 下不可用 |

## 2. 修正口径（后续所有车道适用）

每条前置必须同时验：

1. **可达性**：在**目标文件**里 `#check Kepler.Text.<name>` 能过（在 import 闭包内）；
2. **公理面**：`#print axioms` = `[propext, Classical.choice, Quot.sound]`（出现 `sorryAx` 即 TAINTED）。

任一不满足即记 TAINTED，目标判 BLOCKED。grep 声明体不是判定依据。

## 3. 对 `RANKED.md` 三条建议的影响

- **车道 1 `RRCWNSJ_p26`**：不影响（前置在 LA26 闭包内，`la26-rrcwnsj-w1` 已带强制口径复核）。
- **车道 2 `SCS_4I2_STRAIGHT*` / `MM_4I2`**：不影响（前置在 LA33 自身闭包内）；`la33-straight-w1` 已收到口径警告。
- **车道 3 `la32-4m6`**：**失效**。实测 0/5 全 BLOCKED，根为 `VASYYAU_concl` / `TUAPYYU_concl` / `PWEIWBZ_concl`（LA1）+ `SCS_4T3_IS_SCS_p32`（LA32:247），与上一波 4M7/4M8 的根簇相同。已改发 `la1-roots-recon-w1`（只读，穷举 LA1 registry 根）。

## 4. 由此产生的结论

- LA32 的 4M6 / 4M7 / 4M8 三支共享同一根簇，**逐件修 LA32 是错的顺序**；先解 LA1 registry 根。
- 分诊表里 `dep_status=CLEAN` 的行（`RRCWNSJ_p26` / `SCS_5M2_IMP_SCS_5T1_p29`）仍成立，但**前置清单需按新口径逐条重验**才算绿。

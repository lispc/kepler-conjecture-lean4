# WORK ORDER — `stub-audit`（用户已同意：占位桩审计，只侦察不施工）

> 状态：**用户 2026-11-06 已同意**（"二。同意。"）。
> 性质：**只读侦察**。不写 Lean、不改主仓、不编译。允许 grep / python3 / 读 HOL 源。

## 0. 为什么做

`#10 EXISTS_M_POLYHEDRON` 的教训：**最危险的不是 sorry，是"看起来证完了"**。
`weaklySaturatedP22 := True` 一个桩，让 `weak_saturation` 的证明退化成 `trivial`，
再让 `SATURATE_BALL_ANNULUS`、`DLWCHEM_full`、`XULJEPR_full`（= `fcdjdot` 柱③）一路假绿。
**在修其它东西前，先把这类地雷全找出来。**

## 1. 已知的红旗（起点，不是全集）

| 位置 | 桩 | 后果 |
|---|---|---|
| `PackingAuto22:357` | `weaklySaturatedP22 := True` | `#10` **陈述为假**；`weak_saturation` 证明空；柱③ 假绿 |
| `PackingAuto25:90` | `ox3q1hP25 : Prop := sorry` | `nliOx3q1h` 在"证"一个未知命题 |
| `PackingAuto22:353` | `volSolidTriangleP22 := 0` | 数值桩：不会让命题假，但会让结果**悄悄错** |
| `Assembly:276` | `idsLpIneqs := []` | `LpIneqs := AllCertified []` 空量化恒真 |
| `Assembly:270` + `265-269` | `CertifiedIneqHolds` 表外回落 `True` | 表外键静默变 `True` |
| `IdLists.lean:676/695` | `CertifiedIneqHoldsMirror := True` + 已证的 `…Filled_placeholder` | **假闭合样板** |
| `Assembly:1878/1899/1921/1937/1954` | 5 个 `nli*Ids := sorry` | 无消费者的死声明（锥内不计） |

## 2. 任务

### S1：枚举（要全）
在 `lean/Kepler/` 下找所有可能的桩，至少覆盖五类：
1. `def … : Prop := True` / `:= False` / `:= sorry`
2. `def … : Prop := <另一个 TriviallyTrue 的 def>`（链式）
3. **数值桩**：`def … : ℝ := 0` / `:= 1` / `:= []`，且 docstring 有 `NEEDS` / `Stub` / `PLACEHOLDER`
4. `*P22` / `*_ALT` / `*Stub` 这类"改名镜像"的转接桩
5. `theorem … := trivial` / `:= True.intro` / `:= fun _ _ => trivial`（**证明空但已证**）

> 已知规模：`Kepler/Text/*.lean` 里 "Stub/stub" 提及 **112 处**、`Prop := True/sorry` **3 处**；
> 这是起点不是答案——把**全部**候选列出来。

### S2：判级（每条桩一行）
对每条桩找它的**下游消费者**（`grep` 全树），然后判：
- **F（false）**：让某个"已证"定理或某个被当真的假设变**假**（如 `weaklySaturatedP22`）；
- **V（vacuous）**：让某个"已证"定理的证明**变空**，但命题仍真（如 `weak_saturation`）；
- **W（wrong）**：数值桩，让结果**悄悄错**但不产生假命题（如 `:= 0`）；
- **B（benign）**：有 `NEEDS` 标注、无消费者、或已被上游真件替代。

### S3：优先级
按 `F > V > W > B` 排，并给每条：
- HOL 真身在不在（`reference/flyspeck/` 里能否 grep 到；给 `文件:行号`）
- 修它要动几条下游（blast radius）
- 修它的最小动作（改 def body / 加 import / 退回 sorry / 只加标注）

### S4：结论
一句话回答：**除 `weaklySaturatedP22` 外，还有几个 F 级？分别是哪几个？**
以及"若要一次性清理，建议的顺序"。

## 3. 硬纪律

- **不写 Lean、不改主仓、不编译 Lean**；`/tmp/stubaudit/` 工作；产物 → `~/c17_backup/lane_snapshots/stub-audit/`。
- 每条结论必须可复核：桩的 `文件:行号` + 消费者的 `文件:行号`。
- 不要"顺手修"——这是侦察波。

## 4. 交付

`~/c17_backup/lane_snapshots/stub-audit/{STUBS.tsv,STUBS.md,scripts/,logs/}`。
`STUBS.tsv` 表头逐字：
`stub_file	line	stub_kind	severity	consumers	hol_body	blast_radius	min_fix	notes`

回我 ≤15 行：五类各几条、F/V/W/B 各几条、F 级逐条（位置 + 后果一句话）、
建议清理顺序、以及"除 weaklySaturatedP22 外还有几个 F"。

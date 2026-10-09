# BIEFJHU_explicit 执行波 — 交接（2026-10-10，已闭合）

> 状态：**BIEFJHU_explicit 已闭合落盘**（真路径探针 EXIT=0、error 扫描 0；裸 sorry 29→28，仅闭 BIEFJHU 一处）。
> 证书层全部精确验证（Fraction）。DLWCHEM_sum/XULJEPR_sum 仍按基线原样在 sorryAx 上（其消费的 BIEFJHU 已是真定理，后续波闭合它们是纯增量工作）。

## 落盘记录（2026-10-10）

- `lean/Kepler/Text/PackingAuto22.lean`：基线 1–3030 行 + `PA22g_block.lean`（kit 2235 行 + 已闭合定理）+ 基线 3064–7545 行，共 9747 行。
- 三段 cmp 字节级验证：前段/后段与基线恒同，中段=块；唯一删除 = 基线 3031–3063（旧 docstring+sorry 定理）。陈述冻结，签名逐字未动。
- 探针链：`/tmp/bjf_probe4.lean`（改名块探针）EXIT=0 → `/tmp/PA22_new.lean`（全文件）EXIT=0 → 真路径 `lake env lean lean/Kepler/Text/PackingAuto22.lean` EXIT=0、`grep -icE 'error'`=0。
- sorry 账目：裸 sorry 29→28；含 sorry 行 37→35（减的 2 行都在被替换段）；"declaration uses sorry" 33→32。
- `.lake` olean 未重建（10-08 陈旧 olean 仍在）。探针一律 `lake env lean` 直读源码，不受影响；谁跑全项目 build 谁负责（本波按红线未跑）。

## 本波新雷区（关键，务必读）

1. **重名声明会让 Lean 跳过证明体 elaboration**：探针头 import 基线（含同名 `BIEFJHU_explicit`），块内同名定理在声明头即报 "already been declared"，**证明体从未被检查**。上波 58 错全在 kit；末定理体 14 错是落盘时全文件探针首测才暴露的。探针验证末定理体必须先在 /tmp 副本上改名：
   ```
   sed 's/^theorem BIEFJHU_explicit /theorem BIEFJHU_explicit_gPROBE /' PA22g_block.lean > /tmp/bjf_block_renamed.lean
   ```
2. **`PA22g_gen.py` 只写 `/tmp/bjf_block.lean`，不拷 assets**。改完 gen 必须手动 `cp /tmp/bjf_block.lean docs/biefjhu-assets/PA22g_block.lean` 再探针，否则喂的是陈旧块（本波踩过：asset 停在 10-09 18:25 旧版）。
3. **基线 olean（10-08 13:22）早于源码（10-08 23:17 restored）**，import 探针环境是陈旧 olean。kit 在两环境等价（已双重验证），但最终裁决以全文件源码探针为准。
4. goal 是 `max 0 X` 形时收尾用 `le_max_right`（`le_max_left` 只在 `?_` 延迟统一时侥幸）。
5. 多槽 `refine` 全部改命名参数 + `?name` 槽（位置法错位一次浪费一整轮；本波 hphi/hQ0p/hphiP/hmono 四槽曾整体错位）。
6. `mul_pos` 结论是 `?a * ?b`，对除法形态目标（如 `0 < A·12/↑k`）会造成 by 块拿到 metavar 目标而失败；用 `div_pos`（结论头匹配）+ `have` 显式类型。`positivity` 不读上下文：`0 ≤ T h` 这类含自由变量的目标须结构化拆（add_nonneg/div_nonneg/sqrt_nonneg）。

## 单一生成源工作流（下波入口）

- 改一处即重出块：`python3 docs/biefjhu-assets/PA22g_gen.py` → `cp /tmp/bjf_block.lean docs/biefjhu-assets/PA22g_block.lean` → 探针（末定理体用上面的改名法）。
- 块内容探针命令（kit 层）：
  ```
  cat docs/biefjhu-assets/PA22g_probe_head.lean docs/biefjhu-assets/PA22g_block.lean > /tmp/bjf_probe.lean && printf '\nend Kepler.Text\n' >> /tmp/bjf_probe.lean && (cd lean && ~/.elan/bin/lake env lean /tmp/bjf_probe.lean)
  ```
- 全文件探针（真环境裁决）：`(cd lean && ~/.elan/bin/lake env lean /tmp/PA22_new.lean)`，组装式见落盘记录。

## 历史状态（闭合前存档）

- PA22g_probe20.log：100+ 错 → 58 错（全 kit 层，已全收敛）。
- 证书层结论（全精确）：σ₃=8661/10000；sept 窗 7/10；k=4 用 ser4 级数主控；w4 窗用 sept；k=4→route2(b=11/10)、k=6→route2(b=6/5)；裕度 k=3 0.0239、k=4 0.0154、k=5 0.0029、k=6 0.0059、k∈{7..11} ≥0.0223、tail 0.0474。
- 数学层零改动：所有 route/window/certificate 结论与本波落盘证明一致。

## 本波已修机械错（供复用）

- `Real.sq_sqrt` 在本 Mathlib 是 `(√x)² = x` 形式（√(x²) 需用 `Real.sqrt_sq`）
- `eq_div_iff` 要 `≠ 0`、`div_le_iff₀` 要 `0 <`（不能混用 lt/ne 证明）
- `mul_le_mul` 别名参数序是 `(h₁ h₂ c0 b0)`（第三参是 `0 ≤ c` 即左因子）
- `rw [e]` 的 e 若含 `x/2` 会被 ring_nf 展开成 `x²·(1/4)` 产生残留等式目标
- v1 遗留证明错误三处已修：hsub 缺失、mul_le_mul 参数序、hX2 预算结构；tail v1 hcancel 漏乘 0.26 已修

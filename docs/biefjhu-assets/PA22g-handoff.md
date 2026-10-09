# BIEFJHU_explicit 执行波 — 交接（2026-10-09，诚实收窄：未闭合）

> 状态：**证书层全部收敛（Fraction 精确验证），Lean 体未收敛（58 处 tactic 级机械错，无数学错误）**。
> PA22 基线零触碰（37 sorry 原样），BIEFJHU_explicit 未闭合，DLWCHEM_sum/XULJEPR_sum 仍在 sorryAx 上。

## 单一生成源工作流（下波入口）

- 改一处即重出块：`python3 docs/biefjhu-assets/PA22g_gen.py` → 重出 `PA22g_block.lean`
- 探针命令：
  ```
  cd lean && cat ../docs/biefjhu-assets/PA22g_probe_head.lean ../docs/biefjhu-assets/PA22g_block.lean > /tmp/bjf_probe.lean && printf '\nend Kepler.Text\n' >> /tmp/bjf_probe.lean && ~/.elan/bin/lake env lean /tmp/bjf_probe.lean
  ```
- 上轮终点：`PA22g_probe20.log`，100+ 错 → **58 错**。剩余全为 tactic 级机械错，预估 3–5 轮收敛后按落盘条款全文件探针落盘。

## 逐件状态

| 件 | 状态 |
|---|---|
| ① blockA 修复银行（asn_inc/incle/sept/quad/ser4/双 chord/Tmono） | 证书全过；Lean 体未收敛（kit 约 10 处错） |
| ② route1/route2 银行 | 结构重写完成（修正 v1 的 3 处证明错误），未收敛（约 6 处） |
| ③ w3–w11/wtail 窗口 | 结构完成；w3/w4 主体可闭，w5–w11 两类机械错，未收敛 |
| ④ BIEFJHU_explicit 装配 | 已写（k∈{3,4,5,6}→route2，k∈{7..11}→route1，k≥12→route1+tail），依赖①–③ |
| ⑤ 证书免重算查表 | **完成**（全 Fraction 精确验证，`PA22g_final_certs.py` 可复跑） |

## 证书层结论（全部精确验证）

- σ₃ = **8661/10000**（修正 final2.py 的 433/500 方向违例）
- sept 窗 **7/10**（19/25 处 hex 恒等式为负不可用；9/16=0.5625 处 bracket=+0.2605，7/10 处 +0.0597）
- k=4 弃用 final2.py 的 P4（w⁷/16 系数在 w²=3/8 处 Q²(1−u)<1 不通过）→ 新造 **ser4 级数主控**（w+w³/6+3w⁵/40+5w⁷/112+7w⁹/144，窗 3/8，尾界 d₄u⁴/(1−u)），LP 可行性精确验证，8·poly(6124/10⁴)=5.272745
- w4 窗口改用 sept（同为 √6/4 点），hwin=5.2734
- 路线修正：k=4 双片拆分 hX2b=0.5357 超预算 → route2 但 b=11/10；**k=6 route1 数学不可行**（hmono 上界 0.9007·φ > 0.506）→ route2(b=6/5)
- 最终裕度（全精确）：k=3 **0.0239**、k=4 **0.0154**、k=5 **0.0029**、k=6 **0.0059**、k∈{7..11} ≥0.0223、tail 0.0474

## 剩余 58 错误清单（按块，行号指 probe 文件）

- **chord/chord_b hW2/hWge 尾段（约 10 处，行 316–456）**：`eq_div_iff` 槽位需 `ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 4) (le_of_lt hs3p))` 形式（`le_of_lt hs3p : 0 ≤ √3` 不能直接喂 `lt_of_le_of_lt` 的严格位）；`div_le_div_iff` 两分母 `0 <` 槽已就位，剩 `nlinarith [hS ≤ 2r 链]` 收尾
- **quad hsq（564）**：`hu2p` 未定义（have 需插在 hu3 之前）
- **quad/sept/ser4 hsq 的 `rw [← h3]`（582/692/840）**：h3 是等式，rw 后 `exact h2` 应可，需实测
- **tail_phi（946）**：`nlinarith` 的 hint b0 槽 `by positivity` 待试；备选 `mul_le_mul hτ (le_refl _) hφp (by positivity)` 已就位
- **tail_mono（970/978）**：`mul_nonneg` 链形式待试；h2 的 `by field_simp` 已替换 `by ring`
- **wgen/packs（1374–1869，约 30 处）**：hB2/hsub 的 3 类重复机械错（hB2 括号已修，剩余为 hsub-calc 的 `mul_nonneg` 槽位与 pack hrc 的 `le_sqrt_of_sq_le (by norm_num)` 形式）
- **2121**：probe 特有（import 了含同名公开定理的基线），实块落盘后消失

## 本波新雷区（已修，供复用）

- `Real.sq_sqrt` 在本 Mathlib 是 `(√x)² = x` 形式（√(x²) 需用 `Real.sqrt_sq`）
- `eq_div_iff` 要 `≠ 0`、`div_le_iff₀` 要 `0 <`（不能混用 lt/ne 证明）
- `mul_le_mul` 别名参数序是 `(h₁ h₂ c0 b0)`（第三参是 `0 ≤ c` 即左因子）
- `rw [e]` 的 e 若含 `x/2` 会被 ring_nf 展开成 `x²·(1/4)` 产生残留等式目标
- v1 遗留证明错误三处已修：hsub 缺失、mul_le_mul 参数序、hX2 预算结构；tail v1 hcancel 漏乘 0.26 已修

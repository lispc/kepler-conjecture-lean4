# GRHIDFA 波次计划（WAVES）

> 配套 SCOUT.md §7。行数区间 = 低估–高估（诚实区间）。前置图经 DEP_MAP.tsv 逐行核对。
> 全程无 (d) 真数学缺口（HOL OXLZLEZ2.hl 全证）；风险栏只列工期/装配风险。
> 架构裁定：**证明银行落 PA3（CcV11）**——PA4 import PA3 单向、PA25 消费 PA3 行，
> 反向与双写方案均被否决（SCOUT.md §7）。W1-W5 新行全部插在 PA3:665（`/-! ## OXLZLEZ1:
> main conclusions` 小节头）之前、model 推论段（:664 止）之后；:668-721 的九行结论桩
> 在 W5 末回填真证体，PA3 文件尾部结构不动。

## 波次总表

| 波 | 文件 | 内容（新行数） | HOL 行数 | Lean 估行 | 前置 | 风险 | 成功率 |
|---|---|---|---|---|---|---|---|
| W1 | PA3 | kit 补全：QU_OR_QXY、QX_NN00、QY_NN00、SUM_POS_LT_NUMSEG、SUM_BETA、CC_4CELL_QUQX、NUMSEG_SET_VER、FINITE_INITIAL_SEG(2)、CARD_MOD_NUMSEG、MOD_NUMSEG、THREE_MOD_CONSECUTIVES、MOD_PERIOD_BOUNDED(2)、MOD_INJ11、PI_BOUNDS、periodic_mod1、MOD_ADD_CANCEL、LEAST_BOUND_CC_GG、LITTLE_CC_GG3BB、LITTLE_CC_GG3AA、SUM_NUMSEG 族×5、QX_NN0/QY_NN0 包装（24 行） | 281 | 200–400 | **无（立即可开）**；PA4 同名行 19 枚真证作参考实现 | 低（getD 记账为主，PA3 QUARTER1/CC_CARD2 已趟路） | ~95% |
| W2 | PA3 | 章内小结：oxl6142+CHQSQEY、LXDEYBO、**MTMLSRF**、WKR_COMPTED、UNPNFVW、THREE_LE_CC_CARD（7 行） | 1,199 | 800–1,600 | W1 | 中（MTMLSRF 510 行 12 分裂是全案最大单块；拆两个 checkpoint） | ~80% |
| W3 | PA3 | IPVICGW 支：IPVICGW_C33、UNIQUE_QY、UNIQUE_QY2、IPVICGW_C43_C44、EXISTS_QY_CARD5、CARD5_1074_LE_QYI、**CARD5_LT_1074_QYI（PA4 骨架缺行，需新建陈述）**、PRE_IPVICGW、CC_CARD_LESS_THAN_5、IPVICGW（10 行） | 1,451 | 1,000–1,900 | W1、W2（C33/C43_C44 吃 LXDEYBO/CHQSQEY；UNIQUE_QY 吃 UNPNFVW） | 中（694 行 card5 双件；各自独立 checkpoint） | ~80–85% |
| W4 | PA3 | RSIWAMP、UTEOITF（2 行） | 483 | 350–700 | W3（UTEOITF 吃 IPVICGW+RSIWAMP+UNIQUE_QY） | 低-中（462 行分类，结构规整：nn=3/4/5 三支） | ~85% |
| W5 | PA3 | NOT_QY_LEM、LUIKGMH、GRHIDFA_ALT、**GRHIDFA** + 九大结论桩回填（4 行新 + 9 行回填） | 594 | 450–900 | W4（GRHIDFA_ALT 吃 UTEOITF+IPVICGW；LUIKGMH 吃 NOT_QY_LEM；capstone 吃三件） | 低（capstone 仅 11 行 ARITH；LUIKGMH nn=3 分类 + GRHIDFA_ALT nn=4 MOD-4 计数） | ~90% |
| W6 | PA4 | CC4P4→CcV11 桥（1 桥件 + periodic Prop/Eq 引理）+ 30 行 sorried 桩 discharge（21 CC4P4 行经桥 + 9 `_v11` 孪生 `:= PA3.同名`）+ PackingConcl #print axioms 复核（无编辑） | 0（纯 Lean 侧） | 150–350 | W5 | 低-中（桥的 getD/List vs Fin4/Fin6 记账一次性做对） | ~90% |

**合计：HOL 4,008 定理行（+29 行 tactic/stmt-copy 无需移植）→ Lean 2,950–5,800（中位 ~4,200）。
单工人 3–5 周；双 lane（W2‖W3 分包）2–3 周。**

## 波次间依赖图

```
W1 ──► W2 ──► W3 ──► W4 ──► W5 ──► W6 ──► [PackingConcl 九连转净 / PA25 taint −1 源]
 │            │
 │            └─ W3 内部: C33/C43_C44 ← LXDEYBO/CHQSQEY(W2); UNIQUE_QY ← UNPNFVW(W2)
 └─ W2 内部: UNPNFVW ← MTMLSRF + WKR_COMPTED + THREE_MOD kit(W1)
双 lane 并行切口: W2 与 W3 不得并行（W3 顶部吃 W2 底部），可并行的是 W2 前半（MTMLSRF）
与 W1 收尾；实际推荐 W1→(W2, W3 之 C33/UNIQUE_QY 预备)→W3→W4→W5→W6 串行。
```

## 每波验收处方

- **通用**：`lake build Kepler.Text.PackingAuto3`（W1-W5）/ `…PackingAuto4`（W6）0 error
  0 warning-sorry；每行 docstring 带 HOL 锚（照 PA4 现行格式 `/-- OXLZLEZ2.hl:NNNN. -/`）；
  新行陈述与 HOL goal 逐前提对照（SCOUT §2 流程）；**禁止**为过编译引入任何新 sorry。
- **W1**：24 行全部有 PA4 同名真证行做参考（DEP_MAP.tsv pa4_anchor 列）；
  CARD_MOD_NUMSEG 是其中唯一 PA4 也 sorried 的（PA4:402），照 HOL :1768-1804
  （CARD_EMPTY/CARD_INSERT/FINITE_INITIAL_SEG2/MOD_INJ1 组装，PA4 MOD_NUMSEG:406 真证
  同族习语）。验收锚：`THREE_MOD_CONSECUTIVES` 过即可开 W2（它是 UNPNFVW 的 mod 骨架）。
- **W2**：**checkpoint 2a** = MTMLSRF 单独落地（510 行，前半 :564-800 集合拆分、
  后半 :800-1073 periodic_sum 移位）；**checkpoint 2b** = UNPNFVW + THREE_LE_CC_CARD。
  验收锚：`THREE_LE_CC_CARD` 过（IPVICGW 与 UTEOITF 的公共前件）。
- **W3**：**checkpoint 3a** = IPVICGW_C33 + UNIQUE_QY(2) + IPVICGW_C43_C44（630 行）；
  **checkpoint 3b** = CARD5 双件 + PRE_IPVICGW + CC_CARD_LESS_THAN_5 + IPVICGW。
  注意：CARD5_LT_1074_QYI 是新行（PA4 无桩），陈述照 HOL :2811-2825 冻结：
  `(model∧prep∧real∧sum<0) ∧ cc_card=5 ∧ (∀j, 4cell j → a_spine5+b_spine5*azim j ≤ gg j)
   ∧ cc_qy i ∧ periodic gg card ∧ 0.606≤azim j ∀j ∧ (∑ azim = 2π) ∧ azim i < 1.074
   ⇒ 0 ≤ ∑ gg`——建行时与 PA4 CARD5_1074_LE_QYI:510 的前提表逐条对齐（HOL :2527 与
  :2811 前提同构，仅 1.074 的方向相反）。
- **W4**：UTEOITF 照 HOL :3457-3918 的 ASM_CASES_TAC 骨架（nn=3/4/5 三支；
  首步 `NHANH RSIWAMP` + QY_NN00/QX_NN00 解构）。验收锚：NOT_QY_LEM（PA4:612 已有
  一行式真证体可作 PA3 版本模板：`fun hqy => hqy (UTEOITF cc _hb _hp _hr _hsum i)`）。
- **W5**：capstone 照 HOL :4512-4522：`by_contra` 后对 card 分裂（`DOWNS 3` =
  LUIKGMH 给 4≤card、GRHIDFA_ALT 给 card≠4、RSIWAMP 给 card≤4 → ARITH 爆）。
  九行回填时**只换证明体、陈述零改动**（冻结纪律）。
- **W6**：桥件形态建议 `def toV11 (cc : CC4P4) : CcV11 :=
  ⟨[cc.reals 0, cc.reals 1, cc.reals 2, cc.reals 3], ([cc.bools 0 i = true, …], cc.cardA)⟩`
  （四元素表 getD 对 0-3 指标定义性塌缩）；关键引理
  `cc_bool_model_v11 (toV11 cc) ↔ ccBoolModelP4 cc`（periodic Prop/Eq 经 propext）、
  `cc_real_model_v11 (toV11 cc) ↔ ccRealModelP4 cc`、九个 accessor 引理。
  之后 21 行 CC4P4 桩各 1-3 行 `exact` PA3 对应行经桥；9 枚 `_v11` 孪生
  `:= PackingAuto3.<同名 _concl>`。终检：PackingConcl `#print axioms` 九行
  全 `[propext, Classical.choice, Quot.sound]`（PackingConcl:787-796 现有探针行直接复用）。

## 收益对账（防“波次幻觉”）

- W1-W4 落地期间 **SORRIED 计数零变化**（新行全是 PA3 内部件；PA3/PA4 原 39 枚桩原样）。
- W5 落地：PA3 9→0（九行回填），**首次计分 −9**。
- W6 落地：PA4 OXLZLEZ2 波 30→0（−30），PackingConcl 九连 taint 清（−9 个 sorryAx 流）。
- PA25 侧：PA25.OXLZLEZ 的 taint 源少一个（PA3.GRHIDFA_concl），但 cc_prep_model_data
  (PA25:5238)/cc_real_model_data (PA25:9903) 两枚 sorry 独立于本车道——**勿在本车道记账**。

---

## W1 任务书草案（明天可开工）

**波名**：PA3 OXLZLEZ2-kit 补全（24 行）。
**文件**：`lean/Kepler/Text/PackingAuto3.lean`（唯一施工文件；PA4 只读参考）。
**插入位**：PA3:665 小节头之前新开 `/-! ## OXLZLEZ2: shared kit (OXLZLEZ2.hl:183-3451) -/`。
**参考实现**：PA4:257-598 的 19 枚真证行（CC4P4 版），逐行改写为 CcV11 访问器；
两编码差异只有三点——(i) `cc.reals k i` → `(cc_real_v11 cc).getD k (fun _ => 0) i` 式
访问器（建议先建 `azim cc i`/`gg cc i` 本地缩写，对齐 PA3 现有 cc_azim_v11 等 def），
(ii) `cc.bools k i = true` → PA3 的 Prop 型谓词 `cc_small_v11 cc i` 等（直接同名），
(iii) `periodicPropP4`（Iff）→ PA3 `periodic`（Prop 上的 Eq，定义等价）。

| # | 新行（建议名 = HOL 名） | HOL 锚 | PA4 参考 | 备注 |
|---|---|---|---|---|
| 1 | QU_OR_QXY (cc) (i) | OXLZLEZ2.hl:183-185 | PA4:257 真证 | by_cases bools 5 → by_cases cc_qu_v11 |
| 2 | QX_NN00 / QY_NN00 | :1740-1751 | PA4:374/:380 真证 | PA3 已有单点版 QX_NN:546/QY_NN:553，此为 ∀i 包装 |
| 3 | SUM_POS_LT_NUMSEG | :193-231 | PA4:266 真证 | Mathlib Finset.sum_pos 一行式 |
| 4 | SUM_BETA | :398-402 | PA4:273 真证 | rfl |
| 5 | CC_4CELL_QUQX | :1735-1739 | PA4:362 真证 | 定义展开 |
| 6 | NUMSEG_SET_VER / FINITE_INITIAL_SEG(2) | :1752-1767 | PA4:390/:396 真证 | Mathlib 原生 |
| 7 | CARD_MOD_NUMSEG | :1768-1804 | PA4:402 **sorried**（唯一无参考的大件）| 照 HOL 37 行：CARD_EMPTY/CARD_INSERT 归纳 + MOD_INJ1；PA3 已有 MOD_INJ:425/MOD_INJ1_ALT:451 |
| 8 | MOD_NUMSEG | :1805-1829 | PA4:406 真证 | 消费 7 |
| 9 | THREE_MOD_CONSECUTIVES / MOD_PERIOD_BOUNDED(2) | :1255-1309 | PA4:321/:336/:344 真证 | 消费 MOD_INJ1 |
| 10 | MOD_INJ11 | :2803-2805 | 无行 | MOD_INJ1 柯里化，1 行 |
| 11 | PI_BOUNDS | :2806-2810 | 无行 | `3.14159 < Real.pi ∧ Real.pi < 3.1416`，norm_num |
| 12 | periodic_mod1 | :3354-3360 | 无行 | periodic_mod 特例，7 行 |
| 13 | MOD_ADD_CANCEL | :3373-3378 | 无行 | omega/nat 算术，6 行 |
| 14 | LEAST_BOUND_CC_GG | :3341-3353 | PA4:548 真证 | QU_OR_QXY 三支 + norm_num [cc_eps] |
| 15 | LITTLE_CC_GG3BB / LITTLE_CC_GG3AA | :3361-3430 | PA4:559/:576 真证 | AA 版多 periodic 移位（PA4 版可直接抄） |
| 16 | SUM_NUMSEG2/33/3/44/4 | :3431-3451 | 无行 | Icc 平移和，五连 1-3 行小件 |
| 17 | QX_NN0 / QY_NN0 | :186-189 | 无行 | QX_NN/QY_NN 的 0.0=&0 重述；Lean 无 #0 字面量问题，可跳过或 1 行 alias |

**验收**：PA3 `lake build` 绿；`grep -c sorry` 仍为 9（不多不少）；新行 24 枚全部
带 HOL 锚 docstring；W1 内部无相互 sorry 依赖。
**产出记账**：PA3 +24 真证行（SORRIED 计数不变，资产沉淀）。
**工期**：2-3 施工日（第 7 项 CARD_MOD_NUMSEG 是最大单件，HOL 37 行）。

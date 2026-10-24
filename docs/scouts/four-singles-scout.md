# 四单源 e2e 债测绘 + PA2 污染带（SCOUT，2026-10-23，Lane AX 只读交付）

> 基线：main @ `931306b` 起测；**侦察中途在飞车道落库两笔（08074167 TameLp ykit10、
> 7ca76fa PA25 K4_CC_WI_ALT/K4_CC_WIM 双闭），收尾核查以 HEAD `7ca76fa` 复核全部关键行号**：
> 四源所在文件（PA2/PA3/LA1/LA16）与 PA10/13/14/16/17/19/20/23/24/PackingConcl 两笔提交
> 均未触碰，行号全部有效；受影响仅 PA21（pack def 实为 :963，本稿已改）/PA25/TameLp，
> 其中本稿引用的 PA25 锚（ox3q1hP25:89、OXLZLEZ:9959、GRHIDFA 消费 :9968、
> PACKING_CHAPTER_MAIN_CONCLUSION:9977）与 TameLp:523/:528/:532 经 HEAD grep 逐条复核不变。
> 纪律：**完全只读**——零构建、零 tracked 写、零 git 操作（中途 HEAD 移动系在飞车道所为，
> 非本车道）；全部结论来自 awk/grep 普查 + 逐段精读，无任何编译/axiom 探针（如实声明：
> 涉及 "#print axioms" 的记账一律转引自树内注记，未实测）。交付：本文件 + `DEP_MAP.tsv`
> + `MD5SUMS`（md5 取自 HEAD 7ca76fa 文件）。
> 对照早前车道：docs/scouts/upfzbzm-scout.md（2026-09-29）、upfzbzm-wave2-scout.md（同日）。
> **两份旧侦察的大量上游状态已过时**（KIZHLTL1/2/4、GRUTOTI、AJRIPQN、FINITE_MCELL_SET_LEMMA
> 均已真化），本报告为 2026-10-23 HEAD 的实测刷新。

---

## 0. 结论速览（编排者先读这段）

1. **任务书第 2 条的关键论断实测不成立，必须修正**：`UPFZBZM_concl`（PA2:5565，sorry）
   **不是** PA20/PA24 污染带的根。全树 grep 实测它的**全部代码消费者只有一个**：
   `PA2.RDWKARC_concl`（PA2:5734；PA18/PA19 处出现均为 docstring）。PA20/PA24 的带从
   PA2 **concl 桩族的其他成员**（`MXI_EXISTS_concl`→PA11 私件死代码、`RVFXZBU2_concl`→PA24:4688）
   和 PA10/PA13/PA14 的 i=3 支 sorry 流入，与 UPFZBZM_concl **零定义耦合**。清掉它不会让
   PA20 巨件/REUHADY1 转净一分。
2. **"一件清 → 一批转净"的真实载体是另一件**：`LEFT_ACTION_LIST_PROPERTIES`
   （marchal2.hl:4460）的 S₃-作用移植。它一关三开：PA10 `RVFXZBU` i=3（:488）、
   PA10 `YNHYJIT` i=2/3（:604/:608）、PA14 `QZKSYKG1` i=3（:965）——前两者经
   `PA20.p20g_perm_wit3`（:2080-2116，被 `gammaX_gamma3f` 内部 5 次消费 :2537-2605）
   直通 e2e 巨件 `gammaX_gamma3f`/`gammaX_gamm4fgcy`（均 PROVED，带全在上游）。
   **建议编排者把"PA2 污染带清偿"立项改指此件。**
3. 四源分类（详 §1-§4）：
   | # | 源 | 分类 | 立项判断 |
   |---|---|---|---|
   | 1 | PA3 `GRHIDFA_concl` | (b)机械×GIANT（HOL 全证，纯组合+数值，~3,400 HL 行） | 可开，但属多周巨件；有 PA4 CC4P4 同构桩可互抄 |
   | 2 | PA2 `UPFZBZM_concl` | (c)桥（架构性：PA2 import 成环不可达 PA19 真件） | **值得，但是合并重接线任务（~1 天），不是证题** |
   | 3 | LA16 `JEJTVGB_p16` | (b)机械（HOL 13 行重写装配）| **性价比最高，可立即开**；带一个注册表陈述漂移（§3.4） |
   | 4 | LA1 `main_nonlinear_terminal_v11` | (d)外部锚（deliberate sorry，非缺口） | **不值得**单独立项；它是非线性章 109 条 Main_estimate 不等式的接口占位 |
4. 误植检查：四源冻结陈述与 HOL **零误植**（§5）。发现一处**注册表陈述漂移**（LA1
   `OEHDBEN_concl` 旧形 `{scs6I1}→{scs6T1,scs5M1,scs4M2,scs3T1}` vs JEJTVGB.hl:218 所需
   新形 `…scs3M1}`，LA16:171-179 NEEDS 已记档）——阻塞 JEJTVGB_p16 的 a01 槽，走 SF 通道。
   另发现三处**过时注记**（§5.4）：PA4:1372"RVFXZBU(PA10) 已证"（i=3 仍 sorry）、
   PA24:11228"MXI_EXISTS_concl 欠 r₃<√2 假设"（SF37 已补，PA2:5466-5477 现行形含 guard）、
   PA24:13023/p24_caseB3 docstring"消费 PA2 MXI_EXISTS_concl"（十发波已换接 PA12 真件）。
5. 重大事实刷新（相对 9-29 侦察）：PA16 `KIZHLTL1`(:701)/`KIZHLTL2`(:1064)/`KIZHLTL4`(:1424)
   **全部真证**；PA23 `GRUTOTI`(:6396) 真证（HL 8005 行巨物已清）；PA17 `AJRIPQN`(:931) 真证
   （PA17 全文件 0 tactic sorry）；PA15 仅剩 `SUM_PAIR_2_SET`(:5028)；PA19 仅剩 `RDWKARC`
   (:1071) 一个 tactic sorry（`NEGLIGIBLE_FUNC`:754 已真证）。PA20/PA24 全文件 0 tactic sorry。
6. 消费面：清 #2（重接线）→ `PA2.RDWKARC_concl`（map:100 的 parent）、PA25
   `PACKING_CHAPTER_MAIN_CONCLUSION`（Assembly.lean:6285 消费）各少一跳，仅此而已；
   该臂残余 taint = PA16 `QZYZMJC`(:250) + PA13 `URRPHBZ2`(:364) + PA18 `SUM_GAMMAX`
   骨架（24 处）。清 #3 → LA16 `nonlinear_imp_lp_main_estimate_p16`（:192，已真证的一行式）
   转纯，但该臂仍被 #4 的锚 sorry 染色——**#3 与 #4 必须同波才产生净收益**。
   清 #1 → PA25 `OXLZLEZ`（PA25:9959 真装配）转纯；该臂另欠两枚 bank 叶
   `ox3q1hP25`（map:103）与 `pack_nonlinear_non_ox3q1h`（PA21:963 结构化合取）。

---

# 1. PA3 `GRHIDFA_concl`（map:88，parent = Kepler.Text.OXLZLEZ）

## 1.1 冻结陈述（PackingAuto3.lean:716-721，模块唯一 direct source；PA3 全部 9 处 sorry 均为本行集）

```lean
theorem GRHIDFA_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    False := by sorry
```

同文件姊妹桩 8 枚（:671 CHQSQEY / :678 MTMLSRF / :684 LXDEYBO / :690 UNPNFVW /
:696 IPVICGW / :702 RSIWAMP / :708 UTEOITF / :714 LUIKGMH，全部 `by sorry`）。
PA3 其余内容（CcV11/cc_* defs :43-205、TARJJUW 引理 :206-397、periodicity kit :398-542、
model 推论 :543-664）**全部真证、零 sorry**——PA3 是"定义+工具全证、九大结论全桩"的陈述库模块。

## 1.2 HOL 对位与证明体实测（OXLZLEZ1.hl / OXLZLEZ2.hl）

- 陈述：OXLZLEZ1.hl:173-174（四前提 ∧ gg-sum<0 ⇒ False），与 Lean 逐前提一致（§5.1）。
- `cc_real_model_v11`：OXLZLEZ1.hl:80-133 ↔ PA3:156-205。逐合取对照（gckb/azim_c4/ox3q1h/
  quarters/spine5/… 34 合取）形状一致，HOL 源内注释（`// gckb`、`// ox3q1h`）与 Lean
  合取位次吻合（§5.1 抽查记录）。
- **证明体在 OXLZLEZ2.hl，全证**，实测行数：

| 件 | HL 位置 | 行数 | 内容 |
|---|---|---|---|
| `GRHIDFA`（capstone） | :4512-4515 | 4 | `NHANH LUIKGMH + NHANH GRHIDFA_ALT + NHANH RSIWAMP + ARITH` |
| `GRHIDFA_ALT` | :3919-4231 | **312** | 前两步 `NHANH UTEOITF; NHANH IPVICGW`（**硬消费两姊妹结论**），余为 squ/sqx 分裂 + 常数界求和 + MOD-4 周期计数 |
| `LUIKGMH` | :4249-4510 | **262** | nn=3 分类；kit：NOT_QY_LEM/QY_NN00/QX_NN00/THREE_LE_CC_CARD(:1228)/LEAST_BOUND_CC_GG(:3341)/SUM_BOUND 系/PI_BOUNDS |
| `RSIWAMP` | :3320-3341 | 21 | 短，吃 LITTLE_CC_GG3BB 系 |
| `UTEOITF` | :3457-3919 | **462** | "∀i cc_4cell" 分类 |
| `IPVICGW` | :3308-3320（+链 :1830-3308） | 12（链 ~1,478） | C33(:1830)+C43_C44(:2068)+PRE_IPVICGW(:3229)+CARD5_1074_LE_QYI(:2527,~700) 等 |
| 共享 mod/periodic kit | :1074-1830 | ~756 | MOD_INJ1/CARD_MOD_NUMSEG/MOD_NUMSEG/UNIQUE_QY/NUMSEG_INTER_22/PERIODIC_IMAGE_EQUAL |

- **GRHIDFA_concl 闭链总量 ≈ 3,300-3,400 HL 行**（其中 IPVICGW 链 ~1,490 + UTEOITF 462 +
  GRHIDFA_ALT 312 + LUIKGMH 262 + kit ~756 + RSIWAMP 21）。

## 1.3 树内存量与同构桩

- Lean 侧该链**零移植**（grep `IPVICGW|UTEOITF|LUIKGMH|GRHIDFA_ALT|CARD5_1074_LE_QYI` 于
  Text 全树：仅 PA3/PA4 的 `_concl` 陈述桩命中）。
- **PA4:276-560 有同构 CC4P4（v8-模型）桩链**：LXDEYBO:277/MTMLSRF:283/CHQSQEY:309/
  THREE_LE_CC_CARD:315/UNPNFVW:356/IPVICGW_C33:430/IPVICGW_C43_C44:451/PRE_IPVICGW:524/
  CC_CARD_LESS_THAN_5:530/IPVICGW:536/RSIWAMP:544 —— 同样全部 `by sorry`（小 kit 如
  LEAST_BOUND_CC_GG:551 真证）。即：**两代模型的同一章债务，一个真证都没有**；但 PA4 桩
  的陈述冻结已做，两链可共用一份证明骨架（v8/v11 仅常数表与 card 域差异，见 §5.1）。

## 1.4 折算与波次

HOL 3,400 行 refine 脚本 → Lean 折算 **~2,600-4,600 行**（周期/MOD 计数类折算比高，
纯实数算术折算比低）。建议 4 波：
- W1：共享 kit（MOD_INJ1/CARD_MOD_NUMSEG/MOD_NUMSEG/UNIQUE_QY/NUMSEG 系）~500-900；
- W2：IPVICGW 链（C33+C43_C44+PRE+CARD5_1074_LE_QYI+IPVICGW）~900-1,700；
- W3：UTEOITF + LUIKGMH + RSIWAMP ~700-1,200；
- W4：GRHIDFA_ALT + GRHIDFA 装配（回填 PA3:716 与 PA4 同位桩）~400-800。
风险低（无测度论、无浮点硬点，HOL 逐步可抄），但**工期 2-4 周（单工人）量级**。
双模型同收：W2-W4 产物参数化后同时回填 PA3(v11)/PA4(P4) 两处桩。

## 1.5 立项判断

**可立即开（不欠任何前置），但属最低优先级的"大而钝"件**。理由：体量四源之最、
消费面只有 OXLZLEZ 一跳、且同臂还欠 ox3q1hP25/pack_nonlinear_non_ox3q1h 两个 bank 叶
（各自独立在册）。适合作为后台长波；若编排者要"本周减 SORRIED 计数"，别选它。

---

# 2. PA2 `UPFZBZM_concl`（map:100，parent = Kepler.Text.RDWKARC_concl）——重点，含污染带宽图

## 2.1 冻结陈述与消费面

- PA2:5564-5568：`∀ V, saturated → Packing → cellClusterInequality → TSKAJXY_statement →
  lmfunInequality V → ∃ G, negligibleFun0 G V ∧ fccCompatible G V := by sorry`。
  HOL pack_concl.hl:233-237（= UPFZBZM.hl:52-56 同文）逐前提一致（§5.2，零误植）。
- **全部代码消费者（全树 grep 实测）**：
  1. `PA2.RDWKARC_concl`（PA2:5716，**真证装配** :5720-5822）在 :5734 消费——
     RDWKARC_concl 的其余输入全净（`JGXZYGW_KY_p2`:5697→`PackingJGXZYGW.jgxzygw_p`
     三零、`packingTrans_p2`/`radVPair_p2`/`hlPairAdd_p2`/`setSumCongr_p2`/`setSumImage_p2`
     全真证），taint 唯一来源就是 UPFZBZM_concl；
  2. （间接）`PA25.PACKING_CHAPTER_MAIN_CONCLUSION`（PA25:9979，真装配）:9983 消费
     RDWKARC_concl；`Assembly.lean:6285` 消费后者。
- PA19/PA18 的 "UPFZBZM_concl" 字样（PA19:44/:914、PA18:55/:9654）**全是 docstring**，
  非代码依赖。**PA19.UPFZBZM（:915，真证）走的是 PackingConcl.lean:521 的
  `UPFZBZM_concl_discharged`，不经过 PA2 桩。**

## 2.2 为什么它至今是 sorry：架构性成环

PA2 是底层模块（PA15/PA16/PA19 均反向 import 它）。`UPFZBZM_concl` 的真证内容 =
PA19.UPFZBZM（NEGLIGIBLE_FUNC:754 真证 + FCC:580 真证 + witness），其四输入 =
KIZHLTL1/2/4（PA16）+ SUM_GAMMAX（PA18）+ FINITE_MCELL_SET_LEMMA（PA15）——
**PA2 无法 import 它们**（成环，PA19 header 与多车道注记一致）。因此"在 PA2 里填这个
sorry"不可行；唯一正路 = **合并期重接线**：
- 方案 A（推荐）：`PA25.PACKING_CHAPTER_MAIN_CONCLUSION` 加 `import Kepler.Text.PackingAuto19`
  （实测无环：PA19 imports = PA2/PA12/PA15/PA16/PA18/PackingJGXZYGW，均非 PA25 下游），
  在 PA25 内以 PA19.UPFZBZM + PA2 现成 `_p2` kit 重推 RDWKARC_concl 的 60 行装配
  （PA2:5720-5822 逐行可抄，仅 UPFZBZM_concl 一处换 PA19.UPFZBZM）；PA2.RDWKARC_concl
  与 PA2.UPFZBZM_concl 随 merge 退役。**估 80-140 行、1 个工作日、零新数学。**
- 方案 B：PackingConcl 侧已完成一半（UPFZBZM_concl_discharged:521 → PA19.UPFZBZM），
  但 PACKING_CHAPTER_MAIN_CONCLUSION 在 PA25 不经 PackingConcl——B 不闭合，弃。

## 2.3 PA2 污染带全图（2026-10-23 实测；`*` = map:100 清偿后仍活的入口）

PA2 现存 **26 处 tactic sorry**（:4677 QXSKIIT_concl、:4790 MHFTTZN4_concl、:4798
XYOFCGX_concl、:5391 p3a_gap_tri、:5408-:5885 的 22 枚 `_concl` 桩；XNHPWAB1_concl 与
XNHPWAB4_concl 已于十一发波 2026-10-20 退役删除，见 PA2:5394-5422 注记）。
**活消费图**（括号=消费点）：

```
PA2.XNHPWAB1_concl ──✝ 已退役（十/十一发波换接 PA7.XNHPWAB1 真件，PA7:1772 真证；
                       PA12.OMEGA_LIST_1_EXPLICIT_NEW:1449 注记 "axiom 三零"）
PA2.MXI_EXISTS_concl(:5473, sorry) ──► PA11.mxiExplicit(:843, private)
                       〔死代码：LEPJBDJ 已不消费 mxiExplicit，LA11:58-61 记档；
                         PA20:2031 / PA24:10876 已于十发波换接 PA12.MXI_EXPLICIT(:1968)〕
PA2.RVFXZBU2_concl(:5496, sorry)*──► PA24:4688（p24_edgeX_of_leaf23 链）──► REUHADY1 装配
PA2.GRUTOTI1_concl(:5843, sorry) ──► PA24.GRUTOTI1_concl_p24(:13295)〔consumer-free 沉睡；
                       PackingConcl 2026-10-12 起改走 PA23.GRUTOTI(:6396, 真证, PA23 零 sorry)〕
PA2.L/OXL/KIZHLTL/QZYZMJC/… 其余桩 ──► PackingConcl *_discharged / PA16 等（各成链，不达 PA20/PA24）
```

**PA20/PA24 巨件的实际 taint 入口（与 UPFZBZM_concl 无关）**：
```
marchal2.hl:4460 LEFT_ACTION_LIST_PROPERTIES（S₃-作用，未移植）
   ├─► PA10.RVFXZBU i=3(:488 sorry) ─┐
   ├─► PA10.YNHYJIT i=2(:604)/i=3(:608) ─┤（YNHYJIT 不在 PA20 路径，独立债）
   └─► PA14.QZKSYKG1 i=3(:965 sorry) ─┤
                                       ▼
        PA20.p20g_perm_wit3(:2080-2116)（RVFXZBU:2114 + QZKSYKG1:2112）
                                       ▼
        PA20.gammaX_gamma3f(:2339, PROVED，内 5 次消费 :2537-2605)
        PA20.gammaX_gamm4fgcy(:1613, PROVED，带同族)
                                       ▼
        PA21.TSKAJXY_034（map:95；PA21:10377 消费 gammaX_gamma3f，
        :10399 #print axioms 记账："唯一额外继承 axiom 入口 = gammaX_gamma3f"）
```
另：PA24 `REUHADY1`（:7782 docstring map）——PA24 全文件 **0 tactic sorry**（十三发波
2026-10-20 收口，:7868 记档），残余 taint = `PA2.RVFXZBU2_concl`(:4688 活消费) + 链上
PA13.`URRPHBZ2`(:364, sorry)/`QZYZMJC`。PA21:10390-10391 的记账"live residue the PA2
RVFXZBU concl shims"指的正是这一族（RVFXZBU1/2/3_concl + PA10 本体），**不是 UPFZBZM_concl**。

## 2.4 清偿后的转净清单（诚实账）

- 清 map:100（方案 A）：`PA2.RDWKARC_concl`、`PA25.PACKING_CHAPTER_MAIN_CONCLUSION`
  各减一跳；`PackingConcl.RDWKARC_concl_discharged`（→PA19.RDWKARC:1071，PA19 唯一
  tactic sorry）不受影响、应另行换接 PA2 真装配或 PA25 新件。**PA20/PA24 一件也不转净。**
- 真正"一清转净一批"的两个替代立项（供编排者改指）：
  1. **LEFT_ACTION_LIST_PROPERTIES 移植**（marchal2.hl:4460，HOL 证体在 marchal2；
     ω₂ 在三点胞 circumaxis 投影下的 S₃ 不变性，PA10:409-413/PA14:961-964 双注记定性
     "genuine geometry bite"）→ PA10.RVFXZBU 全件 + PA14.QZKSYKG1 全件 + PA20 双巨件带
     入口全关。折算 ~150-300 行（PA14:849 的 `RVFXZBU_p14`/`upTo4KyLemma_p17` 已证 kit
     提供 i=2 同构先例）。
  2. **PA2.RVFXZBU2_concl**（pack_concl.hl:145-147 同指标胞重合 ⇒ 置换；PA24:4559 记账
     "R3 类 SF-20"）→ PA24 REUHADY1 少一跳。折算 ~60-120 行。

## 2.5 立项判断

`UPFZBZM_concl` 本身：**值得立即做，但按"合并重接线"立项（方案 A，~1 天）**，不要按
"证题"立项。任务书预期"清它 → PA20/PA24 转净"**不成立**；预期中的收益实体是 §2.4 的
两个替代件，建议编排者把污染带清偿波改排这两件。

---

# 3. LA16 `JEJTVGB_p16`（map:89，parent = nonlinear_imp_lp_main_estimate_p16）

## 3.1 冻结陈述（LocalAuto16.lean:180-186）

`theorem JEJTVGB_p16 (h : main_nonlinear_terminal_v11) : JEJTVGB_assume_v39 := by sorry`。
HOL `JEJTVGB`（JEJTVGB.hl:218-230）：`main_nonlinear_terminal_v11 ==> JEJTVGB_assume_v39`。
陈述零误植（§5.3）。消费者：`nonlinear_imp_lp_main_estimate_p16`（:192-195，
`fun h => lp_main_estimate_JEJTVGB_p16.2 (JEJTVGB_p16 h)`，**已真证的一行式**）；
再下游 = `lp_main_estimate`（= JEJTVGB_concl 的 def 别名）进 TameLp（TameLp:523-532 以
`(hmain : lp_main_estimate)` 假设消费）与 Assembly 脊柱。

## 3.2 HOL 证明体（JEJTVGB.hl）与缺口清单

HOL capstone 仅 13 行纯重写：`MATCH_MP_TAC JEJTVGB_case_breakdown` + 22 个
`UNDISCH2` 注册箭头 + `BKOSSGE`。Lean 侧三件套：

| 件 | 位置 | 状态 | 折算 |
|---|---|---|---|
| `scsArrowTransSing_p16` | LA16:125-137 | **真证** | 0 |
| `JEJTVGB_case_breakdown_p16`（23 箭头 ⇒ assume_v39） | LA16:140-177 sorry | HOL JEJTVGB.hl:23-217（195 行 refine；逐支 `SCS_ARROW_TRANS_SING` 回走 + 终局 `EAPGLE`/`scs_arrow_sing_empty`/`s_init_list_alt`/`LFLACKU`） | 150-300 |
| 22 个注册箭头 | LA1 `*_concl` 库（:2476 OEHDBEN、:2481 OTMTOTJ1、…、CUXVZOZ:2680 等） | 全部 sorry，但**以 `h` 为前提的条件件**——JEJTVGB_p16 只消费它们的结论，其 sorryAx 随之流入 | （LA1 侧债，不在本件） |
| `BKOSSGE_p16` | LA16:112-115 sorry | HOL BKOSSGE.hl:304-396（92 行：dist(v0,v1)≤√8 二分，scs_3T5 支经 XWNHLMD_MM、scs_3T1 支经 BBs 展开） | 100-220 |

NEEDS 名录（LA16 头部已记）：Ocbicby.OCBICBY/scs_arrow_sing_empty、Jotswix
s_init_list_alt/LFLACKU、Ayqjtmd.EAPGLE、Ppbtydq.XWNHLMD_MM、Nuxcoea.MMS_IMP_BBS、
is_scs_examples/basic_examples——**其中 LFLACKU_concl（LA1:2676）等在树为 sorried 箭头，
但 case_breakdown 的终局步只需要它们作为 scs_arrow 关系使用**（装配级，非再证级）。

## 3.3 折算与波次

**单波 250-520 行**（case_breakdown 150-300 + BKOSSGE 100-220），前置仅 §3.4 的一个
陈述对齐。成功率 ~85%（纯 scs 记录展开 + 集合论装配，无新数学）。

## 3.4 陈述漂移（SF 通道，单列）

**OEHDBEN 注册表形不匹配**：JEJTVGB.hl 的 a01 槽 = `{scs6I1} → {scs6T1, scs5M1, scs4M2,
scs3M1}`（hexagons.hl:2135 形，LA16:143 a01 冻结同形），而 LA1:2476-2477
`OEHDBEN_concl : scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3T1}` 是 appendix.hl:1394
旧形（尾槽 `scs3T1` ≠ `scs3M1`）。**装配时 a01 不能直接取 OEHDBEN_concl**——需
(a) 证 hexagons 形箭头（若 hexagons.hl:2135 有独立证体则照抄；~40-80 行），或
(b) SF 裁决把 LA1 注册表条目修为 hexagons 形（涟漪 = LA1 注册表消费面 grep 对账）。
LA16:171-179 docstring 已完整记档此事，本侦察实测确认。

## 3.5 立项判断

**立即可开（先落 §3.4 的对齐微件）。性价比四源最高**：体量最小、HOL 逐步可抄、
下游一行式已就位。**但注意净收益捆绑**：清后 `nonlinear_imp_lp_main_estimate_p16` 转纯，
而该臂在 Assembly 的入口仍被 #4（main_nonlinear_terminal_v11 锚）染色——**建议与 #4 的
"锚体替换"同排期**，否则只是把 128 行 SORRIED 换了个名字。

---

# 4. LA1 `main_nonlinear_terminal_v11`（map:102，parent = Kepler.Assembly.textCapstone 直连）

## 4.1 冻结陈述（LocalAuto1.lean:971-975）

```lean
def main_nonlinear_terminal_v11 : Prop := sorry
```

HOL terminal.hl:24-44 `get_main_nonlinear`：**这是 `new_definition`，不是定理**——
把非线性章 Ineq 库中全部 `Main_estimate` 标签不等式的合取定义为一个布尔量。
Lean 侧同构：Assembly.lean:1209 记账"**109 条 Main_estimate 标签**"；
可见盒形由 `LocalAnchors.MainNonlinearTerminalV11`（LocalAnchors.lean:49-54：
`2 ≤ y1..y3 ≤ 2*h0 ∧ cstab ≤ y4 ≤ 3.915 ∧ y5 = y6 = 2`）局部显形。
LocalAnchors.lean:13-14 明文："Every `sorry` is deliberate and marked EXTERNAL-ANCHOR"。

## 4.2 分类与消费面

- 分类 **(d) 外部锚/deliberate**——不是"可证的缺口定理"，而是**非线性/ineq 章未移植的
  接口占位**。清偿 = 把 109 条 Main_estimate 不等式（box ⇒ ineq 形）从 ineq.hl 数据库
  枚举成 Lean 合取并作为 def 体（不等式本身的"证明"= LP 证书/区间算术，属非线性章
  的整章债务，非本锚一件）。
- 消费面（grep 实测）：LA1 内部 `*_concl` 条件箭头族（CUXVZOZ:2680、CJBDXXN:2698、
  ear_acute_p16:284 等 p16 件，及 LA11/LA16/LA19/LA22 的 `(h : main_nonlinear_terminal_v11)`
  参数件——LA16:140/:284/:295/:304、LA22:179/:1464-1568 等）+ `Assembly.lean:219/:267/:292`
  （capstone 接口合取的分量 3/6）。**map:102 直连 textCapstone 正因它是接口合取的分量。**
- 注意与 #3 的捆绑：Assembly 臂上 `lp_main_estimate` 的 taint = JEJTVGB_p16 sorry +
  本锚 sorry 两处；只清 #3 时该臂不减净。

## 4.3 立项判断

**不值得单独立项。** 它是"非线性章移植"这个整章工程的接口投影，单独清它 = 先把 109 条
不等式全部搬进来（而每条的证书链又是章级工程）。编排者应把它视为
**Assembly 接口锚记账项**（同 ox3q1hP25/pack_nonlinear_non_ox3q1h/lp_ineqs 一族），
随非线性章 lane 收口，不进四单源快波。若编排者要"消 map 行"，唯一低fakе路径是：
先把 109 条不等式以 `axiom`-free 的 `def` 合取形落库（陈述搬运，无证明体）——
但每条 box-ineq 的证书仍是章债，SORRIED 计数不会因 def 落库而变净（def 不再 sorry，
但链上 `lp_ineqs` 等兄弟锚仍 sorry）。

---

# 5. 误植检查（零容忍台账）

## 5.1 GRHIDFA_concl —— **无误植**
四前提次序（bool_model → bool_prep → real_model → gg-sum<0）与 HOL OXLZLEZ1.hl:173-174
一致；结论 False 一致；`cc_real_model_v11` 34 合取逐段对位（OXLZLEZ1.hl:80-133 的行内
注释 `// gckb`、`// azim_c4`、`// ox3q1h` 与 PA3:156-205 合取位次一一吻合；抽查
qu-v11 定义 PA3:52 区 vs OXLZLEZ1.hl:52 一致）。注：HOL OXLZLEZ1.hl:159/:162 `RSIWAMP_concl`
let 重复两次（HOL 源自身现象，非误植）；PA4:277-560 CC4P4 桩同形可互为参照。

## 5.2 UPFZBZM_concl —— **无误植**
五前提（saturated/packing/cell_cluster_inequality/TSKAJXY_statement/lmfun_inequality）
+ 结论 ∃G 二合取，与 pack_concl.hl:233-237（=UPFZBZM.hl:52-56）逐字对齐；junk 约定
（negligibleFun0 的 `0 ≤ C` 合取、setSum 有限性 junk、`fccCompatible` 用 voronoiOpen 的
偏差）9-29 侦察已台账，本日无新形差。

## 5.3 JEJTVGB_p16 —— **无误植**；但见 §3.4 注册表漂移（OEHDBEN 新旧形，SF 通道）
JEJTVGB_p16/case_breakdown 的 23 箭头槽与 JEJTVGB.hl:23-217 逐槽对齐（a01 采 hexagons
新形是**忠实**的；漂移在 LA1 注册表侧）。

## 5.4 main_nonlinear_terminal_v11 —— **非误植**（锚 deliberate）；发现 3 处过时注记：
1. **PA4:1372**（MCELL_CELL_PARAMETERS_EXIST 的 NEEDS 块）："TIWWFYQ(PA5)/RVFXZBU(PA10)
   已证"——**陈旧**：PA10.RVFXZBU 的 i=3 支仍 sorry（:488）；YNHYJIT i=2/3 亦 sorry
   （:604/:608）。该 NEEDS 块同时 correctly 记 AJRIPQN 为唯一缺口，但 AJRIPQN 已于 PA17:931
   真证——整块需刷新。
2. **PA24:11228**（p24_caseB2 纠错注记）："PA2 concl-shim 欠 r₃<√2 假设"——**已过时**：
   SF37 已把 guard 补进 PA2:5473-5477（`hl (truncateSimplex 2 ul) < √2` 前提在册），
   PA24:10746 处新注记已反映。
3. **PA24:13023**（p24_caseB3 docstring）："唯一 sorried 上游输入为 PA2 MXI_EXISTS_concl"
   ——**已过时**：十发波（PA24:10876-10879）已换接 PA12.MXI_EXPLICIT。
   （同类：PA24 头部 :80 "upstream SF-20 shim debt PA13 SLTSTLO2/DDZUPHJ" —— PA13 该两件
   现已 tactic 级真证 :3409/:3535，PA13 仅剩 URRPHBZ2:364。）

## 5.5 顺带复核（污染带相关，非四源）
- `MXI_EXISTS_concl`（PA2:5473）vs HOL marchal2.hl:2516 `MXI_EXPLICIT`：pack_concl 接口形
  + SF37 guard，与 PA12.MXI_EXPLICIT(:1968) 语句逐字同形（PA12:1962 记档"语句零改动"）。
  PA24:11223-11230 的"B2 支为假"史注与现行 guard 后的陈述不冲突（B3 支专用）。

---

# 6. 波次与工作量总表（配 DEP_MAP.tsv）

| 波 | 文件 | 内容 | 折算 Lean 行 | 前置 | 风险 | 成功率 |
|---|---|---|---|---|---|---|
| F1 | PA25(+PA19 import) | UPFZBZM 重接线：PA25 内 60 行 RDWKARC 装配重抄，UPFZBZM_concl/RDWKARC_concl 退役 | 80-140 | 无（import 无环已核） | 低 | ~90% |
| F2 | PA10/PA14 | LEFT_ACTION_LIST_PROPERTIES 移植 → RVFXZBU i=3 + YNHYJIT i=2/3 + QZKSYKG1 i=3 | 150-300 | 无 | 中（ω₂ circumaxis 投影几何） | ~80% |
| F3 | LA16(+LA1 微件) | JEJTVGB_case_breakdown_p16 + BKOSSGE_p16 + OEHDBEN 对齐微件 | 250-520 | F-SF（OEHDBEN 形裁决） | 低-中 | ~85% |
| F4 | PA3(+PA4 互抄) | GRHIDFA 闭链 W1-W4（kit→IPVICGW 链→UTEOITF/LUIKGMH/RSIWAMP→GRHIDFA_ALT） | 2,600-4,600 | 无 | 低但长（2-4 周） | ~85% |
| — | 非线性章 | main_nonlinear_terminal_v11 锚体（109 条 Main_estimate） | 章级 | 整章 | — | 不单独立项 |

建议排期：F1（1 天）→ F2（2-3 天）→ F3（2-4 天，含 SF 裁决）；F4 后台长波。
F1+F2 合计可让 map:100 与 map:95 的带入口同时收窄；F3 落地后 LA16 臂仅剩锚 sorry。

# 7. 方法与可复核性

- 模块 sorry 普查命令：`awk '$0 ~ /^[[:space:]]*sorry[[:space:]]*$/{print FNR}' <file>`
  （PA2 额外用 `grep -n "by sorry"`——其 9 桩族为行尾形）。所有行号 = HEAD 931306b 实测。
- 消费面普查：对 24 个 PA2 `_concl` 名逐名 tree-grep（grep -rn … --exclude PA2），
  代码位 vs docstring 位人工分拣（本报告引用处均标注行号）。
- 未做（如实声明）：无编译、无 `#print axioms` 实测（PA21:10399/PA24:7491 等为树内
  在飞车道留下的探针记录，本报告转引并标注）；PA11.LEPJBDJ 的 axiom 纯净度未探针，
  按 PA11 文件 0 tactic sorry + 其 k-case 消费名单记录为"待落波探针"。

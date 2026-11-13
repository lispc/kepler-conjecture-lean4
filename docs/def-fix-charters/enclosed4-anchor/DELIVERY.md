# DELIVERY — enclosed4-w1（LA38 enclosed 集群 5 件 — **1/5 DISCHARGED + 4/5 BLOCKED 判词**，OCBICBY 4T3 收口供料）

车道：`enclosed4-w1`（lean 车道）。基线 HEAD：`93bf9f73`（2026-11-14 开工核面
`git log --oneline -3 -- lean/Kepler/Text/LocalAuto38.lean`，LA38 自 t4crux-w1 后未动；
交付前同命令复核未变）。

## 0. 判词

**PARTIAL：1 件真证交付 + 4 件 BLOCKED（根因 = EXTERNAL-ANCHOR 假桩，非 LP）**。

侦察结论（工单首步）：**5 件没有一件消费 LP 桩 / nli 件**——quad4t3-w1 BLOCKED 表把
「LP 债 6 + enclosed 集群 5 + EXTERNAL-ANCHOR 桩 3」并列，本车道逐件核 statements
与 HOL 出处后细分：**enclosed 集群 5 件的阻塞面是 `_p38` 锚点假桩族
（`enclosedP38`/`cayleyRP38`，LA38:167/:194 `:= sorry`），与 LP 无关**。其中
`IN_V_IMP_AZIM_LESS_PI_ALT` 的陈述里根本不出现 `enclosedP38`，可独立真证（已证，
探针恰标准三）；其余 4 件的结论 literally 是 `enclosedP38 …` 的等式/应用，假桩 opaque
（连 `rfl` 路线都会把 `sorryAx` 注进探针），**在本车道纪律内不可证**，判 BLOCKED 并随
交付附 **DEF-FIX 章程草案 + shadow 实证**（§4），解锁后 sym 两件是机械落库
（证明文本已写好并验证，§4.3）。

## 1. 先决侦察表（逐件）

| # | 件 | LA38 区 | HOL 出处 | 消费 LP? | 消费 `_p38` 假桩? | 判定 |
|---|---|---|---|---|---|---|
| 1 | `enclosed4_lemma` | :2689–2698 | terminal.hl:1623–1740 | 否 | **是**（结论 `= enclosedP38 …`，且链需 `CAYLEYR_5POINTS`——树内无） | BLOCKED（锚桩 + 缺 5 点 Cayley-Menger 件） |
| 2 | `IN_V_IMP_AZIM_LESS_PI_ALT` | :2701–2707 | terminal.hl:1765–1773（引擎 local_lemmas.hl:6247–6264，上游 PRIOR_TO :6216–6244） | 否 | **否** | **DISCHARGED 本车道** |
| 3 | `vv_enclosed4` | :2709–2727 | terminal.hl:1776–1930 | 否 | **是**（结论 `= enclosedP38 …`，上游 enclosed4_lemma） | BLOCKED（锚桩，传递） |
| 4 | `enclosed_sym` | :2729–2734 | terminal.hl:1933–1943 | 否 | **是**（纯 `enclosedP38` 恒等式） | BLOCKED（锚桩；解锁后 7 行可证，已 shadow 验证） |
| 5 | `enclosed_sym2` | :2736–2741 | terminal.hl:1946–1956 | 否 | **是**（同上） | BLOCKED（同上） |

HOL 锚（定义层）：`enclosed` = `sqrt (quadratic_root_plus (abc_of_quadratic (muR …)))`
（leg/enclosed_def.hl:22-24）；`muR` = curried `cayleyR` at squared lengths
（leg/muR_def.hl:40-42）；`cayleyR` = 5 顶点 Cayley-Menger 多项式
（leg/cayleyR_def.hl:32）。**树内已有 canonical 真身**：`IneqClosureDefs.cayleyR`/
`muR`/`abcOfQuadratic`/`enclosed`（IneqClosureDefs.lean:780/:840/:860/:878 区，带
`norm_num` 数值自检与文件尾 axiom 审计），LA38 的 `_p38` 孪生桩按 DEDUP 注记就是
等移植的占位。

## 2. 本次 DISCHARGED 件（patch.diff，LA38 单文件 +74/−3）

**`IN_V_IMP_AZIM_LESS_PI_ALT`**：HOL 证明是单句
`MESON[Local_lemmas.IN_V_IMP_AZIM_LESS_PI]`；其引擎链（PRIOR_TO →
LOCAL_FAN_RHO_NODE_PROS2 → DETERMINE_WEDGE_IN_FAN → LOFA_DETERMINE_AZIM_IN_FA）在
树内**已全部存在**——LA5 的 `_p2` 族（:1044/:3075/:9169/:9185）+ AzimBridge 的
`LocalFan ↔ localFan_p3` 桥（`localFanEquiv_p35`、`localFan_data`）。LA38 原注记
「BLOCKED: PRIOR_TO chain (LOCAL_FAN_RHO_NODE_PROS2 hole)」是旧情报：洞已被
LA5/LA37 填上，缺的只是 import 与族桥。

路线（28 行证明体 + 2 个私有桥 42 行，全 `exact` 无新 sorry）：
1. `LocalFan → localFan_p2`（`localFan_p2.of_localFan_p3 (localFanEquiv_p35.mp hcf.1)`；
   `rhoNode1` 与 `rhoNode1_p2` 同体 defeq，无需桥引理）；
2. `(v, rhoNode1_p2 FF v) ∈ FF`（LA5 `LOCAL_FAN_RHO_NODE_PROS2`）；
3. convex 第二合取给 `w ∈ wedgeInFanGe (v, rho v) E` 与 `azimInFan (v, rho v) E ≤ π`；
4. `_p38` 私有桥 `wedgeInFanGe_eq_wedgeInFanGe_p2_p38`（LA14 W7(g) 同路线：
   `EE_elim` + `AZIM_CYCLE_EQ_SIGMA_FAN_ALT`）+ LA5 `DETERMINE_WEDGE_IN_FAN` 把 wedge
   落成 `wedgeGe_p2` 扇区；`WEDGE_GE_AZIM_LE` 读出 azim 上界；
5. `_p38` 私有桥 `azimInFan_eq_azimInFan_p2_p38`（LA14 W7(f) 同路线）+ LA5
   `LOFA_DETERMINE_AZIM_IN_FA` 把扇区边界读作 `azimInFan`；`le_trans` 收口。

新增 import：`AzimBridge` + `LocalAuto5`（DAG 已核：AzimBridge←LA1/2/3/4/SphereKit，
LA5←LA2/3/TopologyFan，闭包无 LA38，零环）。

**验证**（logs/ 均本车道亲跑，error 计数与 axioms 双检）：
- 直编：`lake env lean /tmp/enclosed4-w1/b/LocalAuto38.final` → **RC=0、error 0**、
  本块行域零 warning（全部 warning 为文件既有位置）；
- 探针（`logs/probe.lean` = 交付文件尾追加 `open Kepler.Text` + `#print axioms`，
  主文件尾零 `#print`）原文（`logs/probe.log`）：
  ```
  'Kepler.Text.IN_V_IMP_AZIM_LESS_PI_ALT' depends on axioms: [propext, choice, Quot.sound]
  ```
- `git apply --check patch.diff` @ HEAD `93bf9f73` → **PASS**（本车道实测）。

## 3. BLOCKED 4 件判词（逐件）

### 3.1 `enclosed_sym` / `enclosed_sym2`（LA38:2729/2736）——锚桩直通
陈述是纯 `enclosedP38` 置换恒等式。HOL 证明 = unfold `Enclosed.enclosed` +
`REPLICATE_TAC 3 AP_TERM_TAC` + `muR_ALT` + unfold `Collect_geom2.cayleyR` +
`REAL_ARITH_TAC`（纯多项式恒等式）。假桩下不可证（opaque，`sorryAx` 污染探针）。
**DEF-FIX 解锁后各 7 行**（证明文本 §4.3 已写好并 shadow 实测 RC=0、探针标准三）。

### 3.2 `enclosed4_lemma`（LA38:2689）——锚桩 + 一件树内缺席的恒等式
HOL 证明（terminal.hl:1636-1740）主线：`CAYLEYR_5POINTS`（5 点 Cayley-Menger，
collect_geom2.hl:61- redo 族）给出 `cayleyR(五点对距²) = 0` 型关系 → `muR_ALT` +
`LTCTBAN`（= 树内 `abc_of_quadratic_cayleyR` 形）把 `muR` 写成二次函数 →
`DISCRIMINANT_OF_CAY`（= `cayleyR_disc`）给判别式 = `16·delta_y·delta_y` →
`Tame_lemmas.delta_y_pos`（树内 `DELTA_Y_POS_4POINTS` LA38:1358 已证）+ chi_msb
符号二分（`CHI_MSB_COPLANAR`/`chi_msb_swap_23`/`chi_msb_additive_d` 等，树内
PackingConcl/PackingAuto18/25 有族件）→ `quadratic_root_plus` 语义（SphereKit 真身）。
**缺件**：`CAYLEYR_5POINTS` 树内无（rg 全库零命中；HOL redo 族
collect_geom2.hl:61-~250 是一条独立移植线）。解锁路径：DEF-FIX（§4）+
`CAYLEYR_5POINTS` 移植（独立工单，估 100–250 行视 HOL 细节）+ chi_msb 族桥装配。

### 3.3 `vv_enclosed4`（LA38:2709）——锚桩传递 + 大叶面（均可解，非 LP）
HOL 证明（terminal.hl:1789-1928）消费：`enclosed4_lemma`（3.2）+
`NONPARALLEL_BALL_ANNULUS40_ALT`（LA38:691 已有 `NONPARALLEL_BALL_ANNULUS40` 真身；
_ALT 变体需核）+ `IN_V_IMP_AZIM_LESS_PI_ALT`（**本车道已证**）+ `vv_rho_node1`/
`vv_azim_le`（LA38 :2494/:2541 已证）+ chi_msb 交换/可加族 + `WEDGE_GE_EQ_AFF_GE`、
`AFF_GE_2_2`（PackingAuto14/15）、`LDURDPN`（LA5/LA14/LA35）、`CONV0_SET2`、
`AFFINE_CONTAIN_LINE`、`Planarity.notcoplanar_imp_notcollinear_fan`、`MOD_INJ1_ALT`。
**全部叶件树内存在**（rg 核名），无 LP。解锁后是一条 ~150–300 行装配线（族桥为主）。
今天不动：上游 enclosed4_lemma 未通之前装配它是空中楼阁。

## 4. DEF-FIX 章程草案（交付物之一：`docs-draft/enclosed4-anchor/`）

> 仅为**草案**，供编排者提交用户审批（比照 tauxkit-w1 章程草案模式；本车道
> 无权自批 def 改动，patch.diff 不含任何 def 体改动）。

- **对象 2 个**（均 EXTERNAL-ANCHOR 假桩，`docs/priority-queue.md` 无在册章程覆盖
  `_p38` 锚桩族；`la-dag-cuts` 仅管声明搬迁）：
  1. `cayleyRP38`（LA38:193-195）：体 := `cayleyR` 多项式逐字移植（源：
     IneqClosureDefs.lean:780，HOL leg/cayleyR_def.hl:32；零新 import 变体）。
  2. `enclosedP38`（LA38:165-167）：**声明块下移到 `muRP38`（:231）之后**
     （Lean 无前向引用），体 := `Real.sqrt (quadraticRootPlus
     (abcOfQuadraticP38 (muRP38 …)).1 … .2.1 … .2.2)`（HOL
     enclosed_def.hl:22-24；孪生形状 = IneqClosureDefs.enclosed :878 /
     LA38 `quadCrossDiag2XP38` :238）。
- **替代变体**（章程内注明）：体 := 别名 `cayleyR x12 … x35` /
  `IneqClosureDefs` kit + LA38 `+import IneqClosureDefs`（本车道 shadow 即此变体；
  IneqClosureDefs 闭包无 LA38，零环；符合 DEDUP「canonical 真身」哲学）。
- **连带账**：`quad_cross_diag2_x_cayleyR`/`muR_ALT`/`muR_alt` 保持 `rfl`（shadow
  实测）；`abc_of_quadratic_cayleyR`/`cayleyR_disc`（LA38:3546/:3555）陈述过
  `cayleytrP38` 桩（**树内无真身**，rg 全库零命中）→ 不在本波，须单独立项；
  净 sorry −4（2 桩体 + 2 定理，每删一笔同 patch 有真证明）。
- **shadow 实证**（`/tmp/enclosed4-w1/shadow/LocalAuto38.lean`，
  `logs/shadow_final.lean`）：桩填真身后 LA38 全文件 RC=0、error 0；两件 sym 证明
  落位后探针原文（`logs/probe_shadow.log`）：
  ```
  'Kepler.Text.enclosed_sym' depends on axioms: [propext, choice, Quot.sound]
  'Kepler.Text.enclosed_sym2' depends on axioms: [propext, choice, Quot.sound]
  'Kepler.Text.IN_V_IMP_AZIM_LESS_PI_ALT' depends on axioms: [propext, choice, Quot.sound]
  ```
- 已知机械坑（shadow 实烧）：`simp only [enclosedP38]`/`congr` 默认 maxRecDepth
  512 会爆（深嵌套多项式），证明需 `set_option maxRecDepth 65536 in`（或 file-level
  option）；两件 sym 的 ring 各 ~2–5 s，无内存压力。

### 4.3 解锁后 sym/sym2 的现成证明文本（shadow 验证过的逐字稿）

```lean
theorem enclosed_sym (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) :
    enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 =
      enclosedP38 y1 y6 y5 y4 y3 y2 y7 y9 y8 := by
  set_option maxRecDepth 65536 in
  unfold enclosedP38
  congr 1
  congr 1
  all_goals simp only [abcOfQuadratic, muR, cayleyR]; ring
```
（`enclosed_sym2` 同型；若章程采用 `_p38` 词汇本体，simp set 换
`[abcOfQuadraticP38, muRP38, cayleyRP38]`——`muRP38`/`cayleyRP38` 方程引理
同样可 unfold，shadow 的别名变体已等价验证此路线。）

## 5. 行数预算

+74/−3（LA38 单文件；预算 ≤450 净增 / ≤150 调用）——余量全部留给解锁波。

## 6. 产物清单

- `patch.diff`（+74/−3，LA38；`git apply --check` PASS @ 93bf9f73）
- `b/LocalAuto38.final`（交付态）、`b/LocalAuto38.lean.start`（起点）
- `logs/probe.lean` + `logs/probe.log`（主探针原文）；`logs/shadow2/3/4.log`
  （shadow 迭代）；`logs/shadow_final.lean`、`logs/probe_shadow.lean` +
  `logs/probe_shadow.log`（shadow 探针原文）
- `docs-draft/enclosed4-anchor/`（DEF-FIX 章程草案：README + gate fence，待编排者
  提交审批）
- 本 DELIVERY.md

## 7. 对账本的勘误 / 情报修正

1. **quad4t3-w1 §3 表**：`enclosedP38`/`taumXP38` 桩注 LA38:167/:182 正确，但
   「enclosed 集群 5 件」的阻塞定性应细分：5 件**均不消费 LP**；4 件卡在
   EXTERNAL-ANCHOR 假桩（本判词），1 件（IN_V_IMP_AZIM_LESS_PI_ALT）**无阻塞已证**。
   「LA38:3546 `abc_of_quadratic_cayleyR`」等两件恒等式另有 `cayleytrP38` 桩阻塞
   （树内无 cayleytr 真身），不属于本波。
2. LA38:2706 旧注记「LOCAL_FAN_RHO_NODE_PROS2 hole」已过时（LA5/AzimBridge 已有
   全套 + 桥）；vv_enclosed4 的 LA38:2726 注记「AZIM_LE_PI_EQ_DIHV (open at
   LocalAuto5:1788)」本车道未消费（本证走 wedge 扇区路线，不经 DIHV），是否仍缺
   留给 vv_enclosed4 工单自核。
3. 主仓 tracked 零改动；未向 `.lake` 写 olean；shadow 全程在 `/tmp` 副本。

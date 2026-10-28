# terminal11-scout — `main_nonlinear_terminal_v11` 109 合取整章拆解报告

- 基线：`4b2ca54ce4ec1b7e782e930d72c10c62c2b605c1`（2026-10-28 12:03 +0800；任务书基线 b226b2a6 之后）。
- 硬约束遵守：主仓 tracked 零写入（工作全程只读；本目录外仅读）；零构建零锁零发射；shell 限 grep/rg/ls/wc/sed -n/awk/file + git 只读 + python3 只读解析。
- 交付：本报告 + `terminal11-inventory.tsv`（109 行）+ `DELIVERY.md` + 中间工件（`extract_109.py`、`records_109.json`、`id_hits.json`、`id_fams.json`、`prep_coverage.json`、`gen_tsv.py`）。

---

## 1. 聚合机制（标的到底是什么）

`main_nonlinear_terminal_v11` **不是手写章节，是数据**。HOL `terminal.hl:26-44`
（`get_main_nonlinear`）的构造：

1. 过滤运行时注册表 `!Ineq.ineqs`，取 tags 含 `Main_estimate` 构造子的全部条目；
2. 按注册表序取 `ind.ineq` 场做左结合合取（`end_itlist (curry mk_conj)`）；
3. `new_definition` 赋名 `main_nonlinear_terminal_v11`（terminal.hl:37）；
4. 消费侧按 ID 取支：`get_main_nonlinear "<idv>"`（如 OWZLKVY0 于 :2253 取
   `6762190381`，EAR_DELTA_X4 于 :2279 取 `8346775862` + `8631418063` 两次换序实例化）。

注册表事实（审计链，与 `lean/scripts/gen_idlists.py` 头注一致）：

- 全项目只有 `nonlinear/ineq.hl` 与 `nonlinear/main_estimate_ineq.hl` 调用 `Ineq.add`
  （build.hl:86-87 先 ineq.hl 后 main_estimate_ineq.hl；`Ineq.add` 前插 ⇒ 注册表序
  = 文本 add 序之逆，main_estimate 条目在表头）。
- 本地章快照（`lean/scripts/local/`）**不含** nonlinear 库——LocalAnchors.lean §1
  所记"章节缺席快照"属实；数据库正本 =
  `reference/flyspeck/text_formalization/nonlinear/{ineq,main_estimate_ineq}.hl`。

### 109 对账：对上了

用项目自带重建器 `gen_idlists.py`（忠实复刻 registry：字面 `add{...}` 块 +
named-add `let iX={...}; add iX;;` + 两处程序化循环）重建后按 `Main_estimate`
过滤，得 **恰好 109 条，且与 `IdLists.lean:369-478
mainNonlinearTerminalV11Ids` 逐条同序一致**（`extract_109.py` 内核级比对通过）。

构成（行号 = 定义处）：

| 源 | 条数 | 说明 |
|---|---|---|
| `main_estimate_ineq.hl` 字面/named add | 69 | 含 `let i…` named-add 家族 |
| `main_estimate_ineq.hl:949-963` make_hex_ear 三重循环 | 35 | `7550003505 i1 i2 i3`，i1≤i2≤i3∈0..4 = C(7,3)；盒恒 `[2,2.52]³×[3.01,3.915]³`，本体由 `mk_ineq_hex` 第 i 支 nth 表生成 |
| `ineq.hl` | 5 | 4717061266(:1698)、5691615370(:2523)、9563139965 d/e/f(:2637/2657/2676) |
| **合计** | **109** | skip 块 8 条（4680581274 delta issue-ups、9507202313 eta/cayleytr0/cayleytr/cayleyR 等）不入库，与 IdLists 一致 |

形态分布：106 条 6 变元（y 空间 88 + x 空间 18，含 `let`-binding 与显式量词形）；
**3 条高维原形**——`4680581274 delta issue-cayleyR`（x1..x10 共 10 变元）、
`…cayleytr`/`…cayleytr0`（x1..x9）。tags 显示验证出处均为 Cfsqp/Xconvert（数值
验证数据库条目，非演绎文本证明）——即 HOL 侧"证明住处"= ineq 数据库 +
数值验证管线，HOL 文本只当不透明假设消费。

## 2. 重合度普查（核心结论）

判定口径四级：{已在 Lean 真证 / 证书在库待粘合 / farm 可发射 / 其他路线}。
普查面：`Interval/Cases/` 证书库、`Assembly.lean` nli* 骨架（94 枚 theorem，
含 nliMainNonlinearTerminalV11/…Ids 两个终端骨架，均 sorry）、`Assembly/IneqPilot.lean`
查表样板、`Assembly/IdLists.lean` 注册表、`Text/LocalAuto*` 19 文件、`Text/LP/W6Data`
（零命中）、`Interval/Cases/GiFactorization.lean`（G_i 符号分解私件，辅助通道）。

### 2.1 分布总表

| 判定 | 条数 | 明细 |
|---|---|---|
| 已在 Lean 真证（证书+粘合+语义命题+查表接线全链） | **0** | 全库唯一接线样板 `3397113841` 属 lp_ineqs 分量，不在本 109 |
| 证书在库待粘合（G4 证书零 sorry，但零语义桥、零接线） | **20** | 原形 1 条：`4717061266`（C4717061266.lean，553 分片，盒=原盒 dyadic 外扩，`orig_op: >`）；prep 形 19 条：2125338128、1117202051、1348932091 delta、2073661826、2171548893、2485876245a/b、3078028960、4559601669、4559601669b、4680581274 delta top issue、4680581274 delta issue-cayleytr0、5550839403 delta、5557288534 delta、6184614449、8346775862、8495326405、8631418063、9368433105 |
| farm 可发射（数据+词汇全备，只差跑发射） | **89** | 直发 54（原形 6 变元，走 3397113841 通道）+ hex 耳模板族 35（一次 for 循环发射 + 单桥共享） |
| 其他路线（经 prep 形） | **2** | `4680581274 delta issue-cayleyR`（10 变元）、`…cayleytr`（9 变元）：prep 已降为 6 变元 x 空间（cayleytr0 的证书即此路线在库先例） |
| 需手写 | **0** | — |
| 需陈述修正（逐条级） | **0** | 接口级 3 项见 §2.3 |

### 2.2 发射可行性证据（为何 89 条是"机械可发"而非"未知数"）

1. **prep.hl 全覆盖**：`prep.hl`（35,546 行，812 条 `prep-<idv>` 条目）含全部
   109 条的准备形（`prep_coverage.json`：109/109 命中，0 缺）。prep 形 = HOL 侧
   已完成 y→x 平方替换 + 盒平方 + 分支规整后的等价形；
   `mk_all_ineq.hl` 在 HOL 里证明 `prepared_nonlinear ↔ nonlinear`。
2. **函数词汇闭包清洁**：对本体符号查 `pipeline/interval/out/defs.json`
   （348 defs / 51 unsupported，后者全是 cone/line/plane 等几何谓词，与 109 无关）：
   `taum`（闭包 13 符号零 unsupported）、`delta_x/delta_y/delta4_y/delta_x4/
   delta4_squared_x`、`eulerA_x`、`atn2`、`cayleytr6u/cayleytr6`、`unit6`、
   `deltaL_x/deltaL_x4`、`flat_term2_234/126/135_x`、`mudLs_234_x/mudLs_135_x`、
   `delta_234/126/135_x`、`tame_table_d`、`tau_residual_x`、`x1_delta_y`、
   `sol0` 全部 DEF。唯一缺口 `mud_234_x_v1/mud_126_x_v1/mud_135_x_v1/mudLs_126_x_v1`
   在 `nonlin_def.hl:495-503` 有定义，只是 ineq.hl-only 的旧解析没走到（pipeline
   对 main_estimate_ineq.hl 从未入参——`ineqs.json` per_file_counts 仅 ineq.hl:181），
   补跑 parse_defs 即机械收录。
3. **同构性实证**：20 条在库证书的头注（`case: prep-<idv> (orig_op …)`）与
   HOL 记录盒/方向逐项吻合（抽样 C4717061266：原盒 `[2,2*h0]⁶ = [2,2.52]⁶`，
   证书盒 `[2, 2705829397·2⁻³⁰]≈[2,2.52]⁶` 外扩；本体 `delta_y>0` ↔ `orig_op: >`）。
   prep 形即 y→x 平方替换（`[2,2.52]→[4,6.3504]`，`delta_y = delta_x∘sq`），
   **prep⇒原形桥是全局一支平方替换引理 + 逐族符号引理，不是逐条手写**。

### 2.3 接口级（非逐条）工作项——侦察新发现

1. **LA1 opaque def 展开**：`LocalAuto1.lean:975 def main_nonlinear_terminal_v11 :
   Prop := sorry` 需替换为 109 支合取（或改查表式 `AllCertified` + 访问器，
   与 HOL `get_main_nonlinear "<idv>"` 同构）。**陈述搬运数据已齐**：
   本快照 `records_109.json` 即逐字清单（编号/盒/本体/序）。
2. **terminal→p21 桥缺失**：LA21:139 `mainNonlinearTerminalV11_p21 := ∀ y,
   MainNonlinearTerminalV11_p21 y` 是"∀y 盒谓词"骨架壳（LocalConcl:493
   `p21_anchor := sorry` 供着），与 LA1 的 terminal_v11 之间**无桥**；
   LA18 还有第三胞胎 `mainNonlinearTerminalV11_p18`（LA21 头注 NEEDS: merge）。
   HOL 的正确模式是按需取支实例化（OWZLKVY0/EAR_DELTA_X4 形），Lean 侧桥应照此写。
3. **prep 证书的桥选择**：19 条 prep 形证书要么补 prep⇒原形桥（全局平方替换
   + 逐族规整），要么对原形重发射（3397113841/4717061266 先例表明发射器吃原形
   y 空间无碍）。二选一是编排决策，不是技术风险。

## 3. 消费者价值核算

### 3.1 数量与语义分类

- HOL 侧（口径 = `lean/scripts/local/` 快照，任务书"164 处"精确对上）：
  **164 处**。terminal.hl 31 处（1 处定义 + 30 处派生引理：OWZLKVY0/2
  （:2240/:2496，`200 ≤ delta_y ⇒ 0 ≤ taum` 家族）、EAR_DELTA_X4、pent/hex
  case 分解、CUXVZOZ/CJBDXXN 的输入件等）；其余 133 处散布 19 文件
  （pent_hex 29、MIQMCSN 23、OCBICBY 15、ARDBZYE 15、JOTSWIX 13、VASYYAU 8、
  hexagons/HIJQAHA 各 5……），全部作不透明前提。reference 树全域另有
  mk_all_ineq.hl 重复定义等 6 处，不入口径。
- Lean 侧（Text/ 19 文件，约 191 处）已按同形携带同一前提——本地章的 Lean
  移植**已经在等这一个 def**：LocalAuto38/32 各 31、LA33 20、LA22 16、LA23 14、
  LocalConcl 11、LA16 11、LA29/LA20 各 8、LocalBridge/LA27/LA1 各 7……

### 3.2 三个具名消费者（触锥判定）

| 消费者 | 位置 | terminal_v11 证成后 | 触锥？ |
|---|---|---|---|
| `CUXVZOZ_concl` / `CJBDXXN_concl` | LA1:2685/:2739 | 边紧引理 `dist (v p1) (v (p1+1)) = 2`（及镜像）。**几何体已真证**：LA21:1186/:1210 `CUXVZOZ_p21`/`CJBDXXN_p21`（除 PQCSXWG1_SYM_p21、simplex_unique_p21 两个 sorry 子件外）；LocalConcl:1026/:1056 `*_discharged` 桥已架（`refine CUXVZOZ_p21 …`）。剩两支 sorry 锚：`mnt11_anchor`（= terminal_v11 本体，LocalConcl:487）与 `p21_anchor`（= ∀y 盒壳，:493）。即：**证成 terminal_v11 只关掉第一支锚**；第二支需 §2.3-2 的取支桥（HOL 中该步是 REAL_ARITH 级实例化，代价小）。 | **是（经边紧→contravening pair 收尾）**，但差一支形态桥 |
| `lp_main_estimate`（JEJTVGB 链） | LA16:488-517 | `JEJTVGB_p16 (h : terminal_v11)` 已按装配形写好；`nonlinear_imp_lp_main_estimate_p16 : terminal_v11 → lp_main_estimate` 已是真推导（`fun h => …`）。terminal_v11 证成即通 M1 账面 lp 分量。 | 账面件（M1 记账），非直接锥路 |
| `OWZLKVY0/2`、EAR_* 家族 | terminal.hl:2240-3944（Lean 侧 LA19/LA38/LocalBridge 携带） | appendix CUXVZOZ/SCS_4I2 等的上游取支引理，全部是 `terminal_v11 ==> 取支 + REAL_ARITH` 形，逐条机械。 | 间接触锥（喂 CUXVZOZ） |

### 3.3 注册表侧

Assembly 骨架 3/3'（`nliMainNonlinearTerminalV11`/`…Ids`，Assembly.lean:1219/:1228）
是 `TheNonlinearInequalities` 六分量合取的第 3 支——terminal_v11 证成 + 查表
填实（IdLists.lean:699 else-True 退化防线须逐条接线）即关 M1 非线性接口的
这 1/6。IdLists 域不变量（六清单并集=查表定义域）已备。

## 4. 处置路线与总量

### 4.1 三类余量

| 路线 | 条数 | 单条成本（runbook 标定） |
|---|---|---|
| A 粘合接线（证书已在库） | 20 | 粘合+语义命题+查表 2-4 h/条（IneqPilot 样板复制）；prep 形 19 条另摊 prep 桥首例 4-8 h（一次）；机器构建已付（olean 回灌即可，C4717061266 553 分片≈6.5h 已付） |
| B farm 直发 | 54（52 单条 + 35 hex 耳族按模板计） | 发射（持机）+ 段建 5-10 机器时/条 + 粘合 2-4 h/条；hex 35 条 = 一次 for 循环发射 + 单桥共享，粘合 1.5-2.5 h/条 |
| C prep 形路线 | 2（cayleyR/cayleytr；cayleytr0 已在 A） | 共享 C 的 prep 桥；各 1 次发射 |
| 接口级 | 3 项 | LA1 def 展开（≤1 天，数据齐备）、terminal→p21 取支桥（1-2 天，HOL 模式照抄）、LA1/LA18/LA21 三胞胎合并（0.5-1 天） |

### 4.2 与 nli farm 六批计划共享

同一机器/模板全共享：`nli-farm-runbook.md` 的七步流程（就绪核查→G4 发射→
CertG 质检→段建→探针→回灌→Glue 落库）、GlueTemplate、跨车道构建锁、
rest-params.tsv 行协议、闸序（全批回灌→glue 绿→探针三→integrate_lane）。
差别仅在输入侧：本 109 的 case JSON 需 pipeline 先吃 `main_estimate_ineq.hl`
（现只吃过 ineq.hl）+ hex 耳 35 条走程序化展开（gen_idlists 已建模，照抄进
prep_queue 即可）。建议作为批族 **T1-T4** 插在 runbook B4 之后：

- **T0（先行，1-2 天，不依赖发射机）**：4717061266 粘合接线首例 + LA1 def
  109 合取展开落库 + `get_main_nonlinear` 访问器与 EAR_DELTA_X4 样例引理。
  产出：黑盒→109 计数债，M1 账面即刻可读。
- **T1**：A 批其余 19 条（prep 证书粘合 + 全局 y2x 桥首例）。
- **T2**：hex 耳 35 条模板批（一次发射 + 单桥，风险最低量最大）。
- **T3**：直发 52 条按盒族分 8-10 批（4-6 条/批），C 2 条随 T1 的 prep 桥。

### 4.3 总量与编排建议（是否值得 M0 前做）

- 机器：89 个新证书 × 中位 5-10 机器时（86 分片/h 标定）≈ **500-700 机器时**，
  跨批流水后墙钟 2-3 周；20 条已付。
- 人工：约 **3-6 人周**（A 批 ≈50-70h；B 直发 ≈104-208h；hex 模板 ≈55-90h；
  接口级 ≈3-4 天）。
- 编排：**M0 前只值得做 T0**（1-2 天，零发射机依赖，把 M1 最大未知数变成
  可计数、可分派的 farm 债并交付 4717061266 单点闭合）；T1-T4 与 nli farm
  B0-B3 共享机器窗口排队，不阻塞 M0。风险集中点：CertG demo 债（挡 bb_arb
  链，runbook 步 3 有预案）、hex 耳族桥首例、p21 形态桥的设计（建议照 HOL
  取支模式做，勿迁就 ∀y 壳）。

## 5. 诚实度备注

- 20 条在库证书的盒/方向经抽样核对（含 4717061266 全项、cayleytr0 形态），
  未逐条全量核对 19 条 prep 证书的盒端点与原盒的 dyadic 覆盖（粘合时端点
  `norm_num` 自会暴露，IneqPilot 模板已内建该检验）。
- "94 枚 nli* theorem"为开工时计数（任务书背景称 77，系他车道推进后的漂移）。
- tags `Deprecated` 条目 `2320951108` 仍在合取内（HOL 数据库如此），如实搬运。

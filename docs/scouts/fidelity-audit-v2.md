# fidelity-audit-v2 — NEEDS 指针接入后的全库保真扫描报告

- 基线: `c200dac95e98`（只读扫描; 主仓零改动、零构建零锁）
- 车道基线注记: 开工时 HEAD = `d0cb83fd`（任务书基线）; 车道进行中并行车落库 4 笔（`8a66cf8a`/`c155edd5`/`3d22d928`/`c200dac9`, 全为 docs/scouts 与 scripts 文档件）, `git diff --name-only d0cb83fd..HEAD -- lean/` 为空——本报告全部数字对两基线同等有效。
- 扫描器: `fidelity_check_v2.py`（本快照目录; import 正本 v1 作回归锚, 正本未动）
- v1 报告参照: `docs/scouts/fidelity-audit-v1.md`（时点 e21a568e: 7779/11201 = 69.4%）

## 方法（v1 → v2 增量）

1. **回归锚**: v1 `pair_decl`/`check_decl` 逐件原样复用; v1 已配对声明的配对与发现逐一保持——锚不被增量扰动。v1 四级路由（docstring 指针 ±6 → 同名/前后缀剥离 → docstring 反引号名 → 大小写不敏感同名）不变。
2. **增量路由**（仅 v1 未配对声明）: 注释指针池 = docstring + 声明头上邻注释链（gap≤2 空行连通, 遇代码行停, docstring 挡停防吞上一件体注） + 声明体内注释（下一 docstring/声明头为界, 即 `sorry` 后的 `-- NEEDS:` 块）。
3. **指针语法/解析增强**: basename 允许连字符（`FNJLBXS-compiled.hl` 类）; basename 先精确后大小写不敏感（`Ajripqn.hl`→`AJRIPQN.hl`、`Local_lemmas.hl`→`local_lemmas.hl` 类; CI 命中多个 basename 视为歧义不解析）。解析语义与 v1 指针路由一致: 包含（±0/2 行容差, 最内起者赢）→ 最近 ≤6 行。
4. **UNRESOLVED**: 解析不了的指针逐条入表（unknown/ambiguous-basename、no-cover）, 声明保持未配对——不造假配对。
5. **冲突抽查**: 已配对声明的池指针若解析到另一 HOL 记录, 记入冲突清单（不改配对, 供人审）。

## NEEDS 指针普查（对照任务书「约 881」口径）

| 口径 | 数 |
|---|---|
| 全库 lean 树（排除 .lake）.lean 文件 | 18961（其中 Text 134; 其余为 Interval/Cases 等机下件） |
| NEEDS 注记单元（含 NEEDS 词法的注释单元, 全库） | 43765 |
| **NEEDS 单元内 `.hl` 提及（含无行号）** | **882 ≈ 任务书 881** |
| 其中带行号指针 `.hl:N`（全库 / Text 内） | 604 / 530 |
| NEEDS 单元数 / `.hl` 提及（Text 内） | 43670 / 800 |
- 结论: 「881」口径 = 全库 NEEDS 注记里 `.hl` 提及总数（本机实测 882, 差 1 属基线漂移级噪声）。其中可参与自动配对的带行号指针 604 条。

## 覆盖率与配对率

| 项 | 数 |
|---|---|
| HOL 文件 / 记录（v1 索引同款） | 408 / 16728 |
| Lean Text 文件 | 134 |
| 扫描的 Lean 声明 | 11331 |
| 其中 sorry 桩 | 1304 |
| v1 锚配对（逐件与 v1 逻辑一致） | 7806 |
| **v2 新增配对（注释指针增量路由）** | **+5** |
| **v2 配对合计** | **7811 / 11331 (68.9%)** |
| 未配对（无正本/派生件） | 3520 |
| UNRESOLVED 指针（未配对件上解析失败） | 167 |
| AMBIGUOUS 指针（归属两可弃用块, 不配对待人判） | 5 |
| 配对冲突抽查命中（不改配对） | 166 |
| v2 路由分布 | anchor:docname=1355, anchor:name=1186, anchor:name-ci=6, anchor:pointer=5182, anchor:pointer~AUEAHEH.hl=1, anchor:pointer~Conforming.hl=1, anchor:pointer~ELLLNYZ.hl=1, anchor:pointer~JGTDEBU.hl=1, anchor:pointer~LVDUCXU.hl=1, anchor:pointer~OXLZLEZ1.hl=2, anchor:pointer~OXLZLEZ2.hl=6, anchor:pointer~UPFZBZM_support_lemmas.hl=1, anchor:pointer~WRGCVDR.hl=4, anchor:pointer~counting_spheres.hl=1, anchor:pointer~fan.hl=6, anchor:pointer~ineq.hl=1, anchor:pointer~leaf_cell.hl=3, anchor:pointer~local_lemmas.hl=11, anchor:pointer~local_lemmas1.hl=4, anchor:pointer~lp_details.hl=2, anchor:pointer~lunar_deform.hl=5, anchor:pointer~marchal2.hl=1, anchor:pointer~marchal3.hl=1, anchor:pointer~merge_ineq.hl=5, anchor:pointer~nonlin_def.hl=3, anchor:pointer~pack1.hl=1, anchor:pointer~pack3.hl=2, anchor:pointer~sphere.hl=2, anchor:pointer~topology.hl=9, anchor:pointer~trig1.hl=1, anchor:pointer~trig2.hl=1, cmt-pointer=5 |

### v1→v2 配对率对账

- v1 报告（e21a568e 时点）: 7779/11201 = **69.4%**。
- v1 逻辑在本基线（c200dac95e98）复算（= v2 锚）: 7806/11331 = **68.9%**——两波次间 +130 声明/+27 配对, 属基线漂移, 非扫描器行为变化。
- v2（NEEDS/注释指针接入后）: 7811/11331 = **68.9%**（+5 件, +0.04 pp）。
- **v1 脚本 :1024 的「配对率推到 ~90%+」预估不成立**, 机理三条:
  1. 882 条 NEEDS `.hl` 提及中带行号指针仅 604, 且绝大多数躺在**已配对声明**的 docstring 里（v1 doc-pointer 路由已消费 5181 对）——NEEDS 注记与 HOL 指针高度伴生, 不是增量矿藏;
  2. 未配对 3525 件中 2987 件为无任何指针线索的装配/派生/机下波直源件（`other` 形态）, 500 件 `_pN` 副本多无独立正本——本来就没有逐件可配对象;
  3. 指针可及的未配对件中, 宽松归属可虚增 ~67 对, 但逐例核验多为**假配对**（`/-!` 段头指针描述整节、前向注记「is defined after that theorem below」、浮动块注讲邻件）——v2 按任务书「不许假配对」原则以块级归属规则排除之, 每条弃用指针进 AMBIGUOUS 表供人判。

## v2 新增配对清单（Lean 锚 → HOL 锚）

| # | Lean 锚 | HOL 锚 | 路由 | v2 发现 |
|---|---|---|---|---|
| 1 | `lean/Kepler/Text/LocalAuto7.lean:1968` `p7w2_hvihvec` | `reference/flyspeck/text_formalization/trigonometry/HVIHVEC.hl:34` | cmt-pointer:Hvihvec.hl:34(doc) | - |
| 2 | `lean/Kepler/Text/LocalAuto9.lean:125` `bEar0_p9` | `reference/flyspeck/text_formalization/local/HDPLYGY.hl:39` | cmt-pointer:Hdplygy.hl:39(doc) | - |
| 3 | `lean/Kepler/Text/LocalAuto9.lean:702` `solLocalFan_p9` | `reference/flyspeck/text_formalization/local/NKEZBFC.hl:36` | cmt-pointer:Nkezbfc.hl:33(doc) | M/DIR |
| 4 | `lean/Kepler/Text/PackingAuto20.lean:1969` `p20g_apex_dist3` | `lean/scripts/packing/marchal2.hl:2516` | cmt-pointer:marchal2.hl:2516(body) | L/NUM_SIGN;M/DIR |
| 5 | `lean/Kepler/Text/PackingAuto21.lean:1037` `p21_h0_lt_hplus` | `reference/flyspeck/text_formalization/nonlinear/nonlinear_lemma.hl:957` | cmt-pointer:Nonlinear_lemma.hl:957(doc) | - |

## 新 H 级发现（v2 增量后全量 H 级, 每条 Lean 锚 + HOL 锚 + 差异）

（无 H 级）

## UNRESOLVED 表（解析不了 → 不配对）

失败原因分布: no-cover=167

| Lean 锚 | 指针 | 原因 | 区 |
|---|---|---|---|
| `lean/Kepler/Text/ConicCapVolume.lean:902` `volumeConicCap` | `GRUTOTI.hl:3356` | no-cover | doc |
| `lean/Kepler/Text/ConicCapVolume.lean:902` `volumeConicCap` | `TSKAJXY3.hl:1959` | no-cover | doc |
| `lean/Kepler/Text/ConicCapVolume.lean:961` `volumeConicCapPos` | `GRUTOTI.hl:7983` | no-cover | doc |
| `lean/Kepler/Text/ContraFan.lean:187` `affGe_0_empty` | `CKQOWSA.hl:115` | no-cover | doc |
| `lean/Kepler/Text/ContraFan.lean:214` `affGe_0_subset` | `CKQOWSA.hl:205` | no-cover | doc |
| `lean/Kepler/Text/ContraFan.lean:272` `annulus_ray_absurd` | `CKQOWSA.hl:131` | no-cover | doc |
| `lean/Kepler/Text/ContraFanDeep.lean:160` `annulus_ray_absurd` | `CKQOWSA.hl:131` | no-cover | doc |
| `lean/Kepler/Text/ContraFanDeep.lean:541` `cf4_cone_inter_imp_segment_conv` | `CKQOWSA_4.hl:4116` | no-cover | doc |
| `lean/Kepler/Text/ContraFanDeep.lean:709` `cf4_not_collinear_smul` | `CKQOWSA_4.hl:2916` | no-cover | doc |
| `lean/Kepler/Text/EulerDerivCore.lean:779` `ea3_core` | `euler_multivariate.hl:372` | no-cover | doc |
| `lean/Kepler/Text/IneqClosureDefs.lean:239` `projX3` | `nonlin_def.hl:44` | no-cover | doc |
| `lean/Kepler/Text/IneqClosureDefs.lean:242` `projX4` | `nonlin_def.hl:46` | no-cover | doc |
| `lean/Kepler/Text/IneqClosureDefs.lean:245` `projX5` | `nonlin_def.hl:48` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto1.lean:336` `scs_v39_explicit` | `appendix.hl:341` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto1.lean:975` `main_nonlinear_terminal_v11` | `terminal.hl:24` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto10.lean:398` `ENF_IMAGE_ITSELF` | `LVDUCXU.hl:2072` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto18.lean:194` `MainNonlinearTerminalV11_p18` | `terminal.hl:24` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto2.lean:555` `p2_IN_V_OF_FAN_EXISTS_DART` | `WRGCVDR.hl:203` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:614` `IS_SCS_IN_V_SY_4_p23` | `JKQEWGV.hl:721` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:621` `IS_SCS_IN_V_SY_5_p23` | `JKQEWGV.hl:1186` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:628` `IS_SCS_IN_V_SY_6_p23` | `JKQEWGV.hl:1668` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:636` `IS_SCS_IN_BALL_ANNULUS_4_p23` | `JKQEWGV.hl:707` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:641` `IS_SCS_IN_BALL_ANNULUS_5_p23` | `JKQEWGV.hl:1329` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:646` `IS_SCS_IN_BALL_ANNULUS_6_p23` | `JKQEWGV.hl:1822` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:663` `IS_SCS_IN_E_SY_5_p23` | `JKQEWGV.hl:1195` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto23.lean:674` `IS_SCS_IN_E_SY_6_p23` | `JKQEWGV.hl:1679` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto3.lean:296` `PAIRS_IN_UNIONS` | `WRGCVDR.hl:238` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto3.lean:325` `V_IN_DARTS_IFF_SWICH_SO_DO` | `WRGCVDR.hl:198` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto3.lean:441` `IN_V_OF_FAN_EXISTS_DART` | `WRGCVDR.hl:203` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto3.lean:519` `CARD_K_FIRST_ELMS_LE_K` | `WRGCVDR.hl:479` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto32.lean:199` `small_nz_p32` | `MIQMCSN.hl:186` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto32.lean:204` `mod_prep_p32` | `MIQMCSN.hl:190` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto32.lean:210` `suc_ex_p32` | `MIQMCSN.hl:195` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1080` `ROW_IN_BALL_ANNULUS_3` | `XWITCCN.hl:1303` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1094` `INEQUALITY_A_B_SCS_TAC_3` | `XWITCCN.hl:1322` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1153` `VV_IN_BALL_ANNULUS_TAC_3` | `XWITCCN.hl:1430` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1159` `PROVE_INEQUALITY_TAC_30` | `XWITCCN.hl:1436` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1165` `PROVE_INEQUALITY_TAC_3` | `XWITCCN.hl:1460` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1478` `PROVE_EQ_V_SY_TAC_4` | `XWITCCN.hl:2464` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1489` `PROOF_E_EQ_IMAGE_4` | `XWITCCN.hl:2481` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1509` `IN_BALL_ANNULUS_ROW_TAC_4` | `XWITCCN.hl:2631` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1518` `INEQUALITY_PROOF_TAC40` | `XWITCCN.hl:2645` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1524` `INEQUALITY_PROOF_TAC4` | `XWITCCN.hl:2657` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1577` `VV_IN_BALL_ANNULUS_TAC_4` | `XWITCCN.hl:2836` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1590` `PROVE_INEQUALITY_TAC_40` | `XWITCCN.hl:2868` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1596` `PROVE_INEQUALITY_TAC_4` | `XWITCCN.hl:2893` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1609` `PROVE_E_SY_EQ_MOD_TAC_4` | `XWITCCN.hl:2913` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1615` `PROVE_E_SY_EQ_IMAGE_VV_4` | `XWITCCN.hl:2921` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1623` `PROOF_E_EQ_TAC_4` | `XWITCCN.hl:2933` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1663` `EQUALITY_V_SY_TAC_5` | `XWITCCN.hl:3247` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1668` `PROVE_V_SY_EQ_5_TAC` | `XWITCCN.hl:3258` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1673` `PROVE_E_SY_EQ_5_TAC` | `XWITCCN.hl:3266` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1679` `PROVE_E_SY_EQ_INV_5_TAC` | `XWITCCN.hl:3290` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1695` `IN_BALL_ANNUUS_TAC_5` | `XWITCCN.hl:3434` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1703` `INEQUALITY_A_B_TAC_50` | `XWITCCN.hl:3448` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1709` `INEQUALITY_A_B_TAC_5` | `XWITCCN.hl:3461` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1752` `VV_IN_BALL_ANNULUS_TAC_5` | `XWITCCN.hl:3654` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1765` `PROVE_INEQUALITY_TAC_50` | `XWITCCN.hl:3661` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1771` `PROVE_INEQUALITY_TAC_5` | `XWITCCN.hl:3689` | no-cover | doc |
| `lean/Kepler/Text/LocalAuto36.lean:1776` `V_SY_EQ_IMAGE_VV_TAC5` | `XWITCCN.hl:3703` | no-cover | doc |

（其余 107 条见 TSV/脚本输出, 同因重复）

## 配对冲突抽查（已配对件的池指针另有所指; 不改配对, 人判清单）

| Lean 锚 | v1 配对 | 池指针另指 | v1 路由 |
|---|---|---|---|
| `lean/Kepler/Text/ConformingAuto1.lean:262` `hypermapOfFan_faceMap_eq_ca1` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | pointer:fan.hl:2780 |
| `lean/Kepler/Text/ConformingAuto10.lean:182` `setOfEdge_eq_of_add_edge` | `reference/flyspeck/text_formalization/fan/fan.hl:423` | `reference/flyspeck/text_formalization/fan/fan.hl:2101` | pointer:fan.hl:423 |
| `lean/Kepler/Text/ConformingAuto10.lean:399` `SIGMA_FAN_OF_FANADD_AT_POINT1` | `reference/flyspeck/text_formalization/fan/fan.hl:423` | `reference/flyspeck/text_formalization/fan/fan.hl:2101` | pointer:fan.hl:423 |
| `lean/Kepler/Text/ConformingAuto10.lean:510` `SIGMA_FAN_OF_FANADD_AT_POINT2` | `reference/flyspeck/text_formalization/fan/fan.hl:423` | `reference/flyspeck/text_formalization/fan/fan.hl:2101` | pointer:fan.hl:423 |
| `lean/Kepler/Text/ConformingAuto12.lean:337` `f1Fan_eq_fFanPair_of_dart1_auto12` | `reference/flyspeck/text_formalization/fan/fan.hl:2469` | `reference/flyspeck/text_formalization/fan/fan.hl:2174` | pointer:fan.hl:2469 |
| `lean/Kepler/Text/ConformingAuto12.lean:455` `card_ds2_fanadd_eq3` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | `reference/flyspeck/text_formalization/hypermap/hypermap.hl:274` | pointer:fan.hl:2694 |
| `lean/Kepler/Text/ConformingAuto12.lean:596` `reperentation_of_ds2` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | `reference/flyspeck/text_formalization/hypermap/hypermap.hl:274` | pointer:fan.hl:2694 |
| `lean/Kepler/Text/ConformingAuto12.lean:935` `exists_tranf_fan` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4094` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto12.lean:935` `exists_tranf_fan` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:171` `unique_tranf_fan` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:407` `INJ_TRANF_FACE_DELETE_DS` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:769` `SUR_TRANF_FACE_DELETE_DS` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:769` `SUR_TRANF_FACE_DELETE_DS` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:1033` `DOMAIN_TRANF_FACE_DELETE_DS` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2780` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto14.lean:1033` `DOMAIN_TRANF_FACE_DELETE_DS` | `reference/flyspeck/text_formalization/fan/Conforming.hl:4097` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | pointer:Conforming.hl:4097 |
| `lean/Kepler/Text/ConformingAuto7.lean:240` `rep_node_set_fan` | `reference/flyspeck/text_formalization/fan/fan.hl:2694` | `reference/flyspeck/text_formalization/fan/fan.hl:1005` | pointer:fan.hl:2694 |
| `lean/Kepler/Text/ContraFan.lean:786` `ESTD_fan6` | `reference/flyspeck/text_formalization/tame/CKQOWSA.hl:79` | `reference/flyspeck/text_formalization/tame/CKQOWSA_4.hl:45` | pointer:CKQOWSA.hl:79 |
| `lean/Kepler/Text/EulerAssembly.lean:215` `ea4_eulerP` | `reference/flyspeck/text_formalization/general/sphere.hl:394` | `reference/flyspeck/text_formalization/general/sphere.hl:387` | pointer:sphere.hl:394 |
| `lean/Kepler/Text/EulerAssembly.lean:539` `ea4_sol_x_sol_euler_x` | `reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl:841` | `reference/flyspeck/text_formalization/general/sphere.hl:735` | pointer:merge_ineq.hl:841 |
| `lean/Kepler/Text/EulerAtn2Kit.lean:221` `ea1_sol_euler_x_sqrtdelta` | `reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl:1060` | `reference/flyspeck/text_formalization/general/sphere.hl:735` | pointer:merge_ineq.hl:1060 |
| `lean/Kepler/Text/IneqClosureDefs.lean:95` `dihXDivSqrtdeltaPosbranch` | `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:138` | `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:132` | pointer:nonlin_def.hl:138 |
| `lean/Kepler/Text/IneqClosureDefs.lean:136` `ldihXDivSqrtdeltaPosbranch` | `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:144` | `reference/flyspeck/text_formalization/general/sphere.hl:525` | pointer:nonlin_def.hl:144 |
| `lean/Kepler/Text/IneqClosureDefs.lean:173` `solEulerXDivSqrtdelta` | `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:115` | `reference/flyspeck/text_formalization/general/sphere.hl:827` | pointer:nonlin_def.hl:115 |
| `lean/Kepler/Text/LocalAnchors.lean:49` `MainNonlinearTerminalV11` | `reference/flyspeck/text_formalization/local/terminal.hl:2239` | `reference/flyspeck/text_formalization/local/terminal.hl:2496` | pointer:terminal.hl:2240 |
| `lean/Kepler/Text/LocalAnchors.lean:49` `MainNonlinearTerminalV11` | `reference/flyspeck/text_formalization/local/terminal.hl:2239` | `reference/flyspeck/text_formalization/local/appendix.hl:1514` | pointer:terminal.hl:2240 |

（其余 141 条从略）

## AMBIGUOUS 表（块级归属规则弃用、但指针可解析的注记 — 归属两可, 人判）

| Lean 锚（本件未配对） | 弃用块指针 | 指针解析到 |
|---|---|---|
| `lean/Kepler/Text/LocalAuto3.lean:231` `permutesF_p3` | `WRGCVDR.hl:341` | `reference/flyspeck/text_formalization/local/WRGCVDR.hl:347` |
| `lean/Kepler/Text/LocalAuto3.lean:441` `IN_V_OF_FAN_EXISTS_DART` | `WRGCVDR.hl:341` | `reference/flyspeck/text_formalization/local/WRGCVDR.hl:347` |
| `lean/Kepler/Text/PackingAuto2.lean:5380` `p3a_gap_tri` | `pack_concl.hl:66` | `lean/scripts/packing/pack_concl.hl:66` |
| `lean/Kepler/Text/PackingAuto9.lean:436` `p9_omega_descent_step` | `NJIUTIU.hl:149` | `lean/scripts/packing/NJIUTIU.hl:149` |
| `lean/Kepler/Text/PackingAuto9.lean:436` `p9_omega_descent_step` | `NJIUTIU.hl:27` | `lean/scripts/packing/NJIUTIU.hl:27` |

典型: `PackingAuto9.lean:574` `-- DISCHARGES: (NJIUTIU.hl:149…)` 隔一空行脱离 `p9_omega_descent_step` 证明体且紧邻下一件 docstring, 按规则不归本件（若归属属实则是本表漏收一对, 人判补）; 反向教训: `LocalAuto3.lean:234` 同形态前向注记若收纳会产出两起假配对（`permutesF_p3`/`IN_V_OF_FAN_EXISTS_DART` ← `choose_nd_point`）, 已由本规则拦截。

## Top-5 人审遗留的 v2 复核（四条 + SF-53 对照）

1. **SphereKit `num1`（v1 M/NUM_SIGN「Lean `4`×1 vs HOL `-4`×1」）→ RESOLVED（SF-58）**。SF-58（`956d75ec`, 2026-10-27 双闸落库）已把重建体补回 HOL 正本项; v2 HEAD 现场核对: `SphereKit.lean:143-145` `-4 * (x4 ^ 2 * e1 + 8 * (x5 - x6) * (e2 - e3) - x4 * (16 * e1 + (x5 - 8) * e2 + (x6 - 8) * e3))` 与 HOL 正本（v2 现配对锚 `sphere.hl:821`, 即 v1 时点锚 `test_flyspeck.hl:95` 的同式副本）`-- &4*((a2 pow 2)*e1 + &8*(b2-c2)*(e2-e3) - a2*(&16*e1 + (b2-&8)*e2 + (c2-&8)*e3))` 逐项同号同构（两处负号 `-4`、`- x4(…)` 布局一致）。v2 全量扫描对该声明零发现。**定 RESOLVED**。
2. **ContraFanDeep:3598 `cf4_etaP_box` → FALSE-POSITIVE（维持, 机理修正）**。v1 锚 `Inequalities.hl:356` = `ETA_Y_4_POINTS_INEQ`（eta_y 盒式命题, 常数 `&2`×7/`#2.2`）; Lean 件是其**证明内核重述**——docstring 自述「W3a 核心（HOL `ETA_Y_4_POINTS_INEQ` 的盒式内核, Inequalities.hl:356-372）」, 内容为 `P a b c := (11/5)·upsX a b c − a·b·c` 在盒 `[4, 6.3504]³` 非负（`6.3504 = (2·h0)²`, 角点法证）。人审「疑引错条目」应修正为「条目引用正确（证法母体）, 声明性质为派生证明件」——启发式在「内核 vs 命题」编码差上必然报数值不等, 非误植。**维持 FALSE-POSITIVE**。
3. **LocalAuto11:192 `dartStd4_p11` → 截断移植嫌疑不成立（错配伪影 + 刻意不透明桩）**。v1 报「正本三常数（0.206/0.7573/1.433）在 Lean 陈述中缺失」。v2 复核: 该件是**刻意不透明签名桩**（docstring: 「HOL `dart_std4` (Ineq.hl, not in the corpus)…only the signature is needed…the value is carried opaquely」）, stmt 体为 `sorry`; v1 的 HOL 锚 `lp_details.hl:1431` 实为 `quad_4240815464_a` 的 ineq 条目（三常数属于它, 经 docstring 反引号名路由错配到桩）, 真锚 `Ineq.hl` 不在语料。**结论: 非截断移植; 错配伪影, 桩待 Ineq 波落地后自然消解**。
4. **PA21 `bank_BIXPCGW9455898160` docstring（:599-600, 声明现行号 :601）→ 确认（注释级; 陈述无恙）**。v2 HEAD 现场核对: 陈述 `gamma4fgcy … > -0.00569` 与 HOL `ineq.hl:985` `> -- #0.00569` 一致（SF-49 修复保持, v2 扫描对该件零数值发现; v2 锚 `pointer:ineq.hl:985` → `ineq.hl:982` 记录不变）; docstring 括注「双重负号 = 0.00569」仍错——HOL `--` 是一元负号 token, `-- #0.00569` = −0.00569, 括注把它读成 +0.00569, 与已修陈述自相矛盾。**维持「注释级勘误」建议（SF 候选, 不涉陈述改动）**。
5. （对照）**SF-53 两处**: 本基线已修（`PackingAuto4.lean` 现为 `Icc 0 (ccCardP4 cc - 1)` 与 HOL `0..cc_card_v11 cc - 1` 对齐; `CARD5_1074_LE_QYI` 同）, v2 扫描正确不报; `--selftest` 以回放验证检测器仍能在回置误植时双双抓到 H/RANGE。

## 自检结果

`python3 fidelity_check_v2.py --selftest` — **PASS**（退出码 0）:
1. **SF-53 基线自适应回放**: 本基线已修 → 修复态正确不报; 回置误植（去 `- 1`）后 `ccRealModelP4` 与 `CARD5_1074_LE_QYI` 均以 H/RANGE 抓到。
2. **SF-49 回放**: PA21 `> -0.00569` 回置为 `> 0.00569` 后, 以 H/NUM_SIGN「同值反号」抓到 `bank_BIXPCGW9455898160`。
3. **锚等价**: v1 `pair_decl` 幂等（v2 锚阶段直接复用同函数）。
4. **解析增强**: `Ajripqn.hl:89`→`AJRIPQN.hl`、`Local_lemmas.hl:100`→`local_lemmas.hl` 大小写回退命中; 未知 basename 返回 unknown 不给假配对。

## 已知误报类型（人工复核先排除; 1-7 沿用 v1 报告）

沿用 v1 七类（DIR/PREM 结构性编码差、NUM_SIGN 内联重述/标识符引用、RANGE 拆分合并、NO_HOL 派生件、指针 ±6 容差、float.hl 机器证书、定义体表达式 vs 字面常数）。v2 新增两点:
8. **v2 新增对的 `cmt-pointer/needs-pointer` 路由**: 上邻链/体注为v1 未用的证据面, 抽查 5 对均人核通过, 但 M 级 DIR/NUM_SIGN 噪声性质同 v1;
9. **AMBIGUOUS/冲突清单是缓冲不是缺陷**: 弃用块与另指指针均不改变配对, 供下一轮人判。


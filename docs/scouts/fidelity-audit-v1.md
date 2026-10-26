# fidelity-audit-v1 — Lean 陈述保真静态扫描报告

- 基线: `e21a568e9698`（`git rev-parse HEAD`, 只读扫描, 未改任何文件）
- 扫描器: `lean/scripts/fidelity_check.py`（纯 Python 3 标准库）

## 方法

1. HOL 索引: `lean/scripts/packing/*.hl` + `reference/flyspeck/text_formalization/**/*.hl`，解析 `let N = prove(_by_refinement)(\`goal\`)`（含 `prove(N_concl)` 间接引用解析）、`new_definition`、`let N = \`…\``、ineq.hl `add { idv=…; ineq=all_forall \`…\` }` 四种形态；注释（`(* *)`、`//`）与 ML 字符串先抹除再抽常数。
2. Lean 解析: `lean/Kepler/Text/*.lean` 全部 `theorem/lemma/def/abbrev` 声明；`def/abbrev` 仅收 `: Prop` 与数值类型（ℝ/ℕ…）体；docstring（`/-- … -/`）单独保留作配对线索，不参与常数抽取；块注释/行注释抹除。
3. 配对优先级: docstring 中 `XXX.hl:行` 指针（±6 行容差）→ Lean/HOL 同名（含 `bank_` 前缀与 `_p4/_alt/_concl` 后缀剥离）→ docstring 反引号名 → 大小写不敏感同名。
4. 启发式: NUM_SIGN（带符号常量多重集，0/1 忽略；同值反号 → H）、RANGE（`Icc/Ico/range` 上界 `-1` 形态与 HOL `0..n-1` numseg 逐位对齐，形态不符 → H/M）、DIR（比较符多重集，ineq-box 记录跳过）、PREM（`==>`×n vs `→`×n 差 ≥3，L）、NO_HOL（未配对桩，L）。

## 覆盖率

| 项 | 数 |
|---|---|
| HOL 文件 / 记录 | 408 / 16728 |
| Lean Text 文件 | 134 |
| 扫描的 Lean 声明（含 def Prop/ℝ） | 11201 |
| 其中 sorry 桩 | 1376 |
| **配对成功** | **7779 / 11201 (69.4%)** |
| 无正本（未配对） | 3422 |
| 配对路由 | docname=1330, name=1186, name-ci=6, pointer=5181, pointer~AUEAHEH.hl=1, pointer~Conforming.hl=1, pointer~ELLLNYZ.hl=1, pointer~JGTDEBU.hl=1, pointer~LVDUCXU.hl=1, pointer~OXLZLEZ1.hl=2, pointer~OXLZLEZ2.hl=6, pointer~UPFZBZM_support_lemmas.hl=1, pointer~WRGCVDR.hl=4, pointer~counting_spheres.hl=1, pointer~fan.hl=6, pointer~ineq.hl=1, pointer~leaf_cell.hl=3, pointer~local_lemmas.hl=11, pointer~local_lemmas1.hl=4, pointer~lp_details.hl=2, pointer~lunar_deform.hl=5, pointer~marchal2.hl=1, pointer~marchal3.hl=1, pointer~merge_ineq.hl=5, pointer~nonlin_def.hl=3, pointer~pack1.hl=1, pointer~pack3.hl=2, pointer~sphere.hl=2, pointer~topology.hl=9, pointer~trig1.hl=1 |
| 报告（按类） | DIR=2805, NO_HOL=8, NUM_SIGN=2641, PREM=612, RANGE=234 |
| 报告（按级） | H=2, L=3024, M=3274 |

## 已知误报类型（人工复核时先排除）

1. **DIR/PREM 结构性编码差**: Lean 把 HOL 的 `!i. A i ==> B i` 前提改写成显式 binder （`∀ i, A i → B i →`），`==>`/`→` 计数天然不等；ineq.hl 的 `[box]` 前提已折入 Lean 的 `≤` 链（ineq 记录已跳过 DIR/PREM，但普通记录仍有此噪声）。
2. **NUM_SIGN 的 `仅HOL/仅Lean`（M 级）**: Lean 常把别处定义的常数内联重述（如把 `cc_real_model_v11` 的合取项展开），或反过来引用标识符（`aSpine5P4` vs `a_spine5` 不比数字）。
3. **RANGE 个数不等（M 级）**: Lean 有意拆分/合并求和（如二分装配），不必然是误植。
4. **NO_HOL（L 级）**: `bank_*` 投影、`_alt`、装配辅助桩是派生件，本来就没有同名正本。
5. **指针 ±6 行容差**可能配到邻近定理（瘦文件内定理密集时）。
6. **`reference/.../jordan/float.hl` 机器生成证书引理**: 该文件是浮点评估证书（目标里直接嵌 `#36.1` 一类常数），与其同名的 Lean 几何重述天然数值不等——凡 hol_file 落在 float.hl 的 NUM_SIGN M 一律先按此类排除。
7. **定义体为表达式的常数**: Lean 用 `2*h0-2`、HOL 用字面 `#0.52`（h0=1.26）等编码差会报「仅HOL/仅Lean」，语义相等。

## Top 30 可疑项（人读表）

1. **[H/RANGE] `lean/Kepler/Text/PackingAuto4.lean:197` `ccRealModelP4`** ← `lean/scripts/packing/OXLZLEZ1.hl:80`
   - 为何可疑: 界 off-by-one 形态: HOL 上界偏移 -1 (`..cc_card_v11 cc`) vs Lean 上界偏移 +0 (`..ccCardP4 cc`) — SF-53 类
   - Lean: `periodicP4 (ccAzimP4 cc) (ccCardP4 cc) ∧ periodicP4 (ccGgP4 cc) (ccCardP4 cc) ∧ periodicP4 (ccGg3aP4 cc) (ccCardP4 cc) ∧ periodicP4 (ccGg...`
   - HOL: `cc_real_model_v11 cc <=> periodic (cc_azim_v11 cc) (cc_card_v11 cc) /\ periodic (cc_gg_v11 cc) (cc_card_v11 cc) /\ periodic (cc_gg3a_v11 ...`
2. **[H/RANGE] `lean/Kepler/Text/PackingAuto4.lean:519` `CARD5_1074_LE_QYI`** ← `lean/scripts/packing/OXLZLEZ2.hl:2527`
   - 为何可疑: 界 off-by-one 形态: HOL 上界偏移 -1 (`..cc_card_v11 cc`) vs Lean 上界偏移 +0 (`..ccCardP4 cc`) — SF-53 类
   - Lean: `theorem CARD5_1074_LE_QYI (cc : CC4P4) (i : ℕ) (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧ ccRealModelP4 cc ∧ Finset.sum (Finset.Icc 0 (ccC...`
   - HOL: `(cc_bool_model_v11 cc /\ cc_bool_prep_v11 cc /\ cc_real_model_v11 cc /\ sum (0..cc_card_v11 cc - 1) (cc_gg_v11 cc) < &0 ) /\ (!i. cc_4cel...`
3. **[M/NUM_SIGN] `lean/Kepler/Text/SphereKit.lean:144` `num1`** ← `reference/flyspeck/azure/test_flyspeck.hl:95`
   - 为何可疑: 同值反号: Lean `4`×1 vs HOL `-4`×1 — SF-49 类符号误植 （小整数系数位反号, 注意 `-(…)` 括号负号移位类误报）
   - Lean: `4 * ((16 * x4 - x4 * x4) * e1 + (x5 - 8) * x4 * e2 + (x6 - 8) * x4 * e3)`
   - HOL: `num1 e1 e2 e3 a2 b2 c2 = -- &4*((a2 pow 2) *e1 + &8*(b2 - c2)*(e2 - e3) - a2*(&16*e1 + ( b2 - &8 )*e2 + (c2 - &8)*e3))`
4. **[M/NUM_SIGN] `lean/Kepler/Text/ConformingAuto23.lean:207` `not_mem_line_of_notCoplanar`** ← `reference/flyspeck/text_formalization/jordan/float.hl:1553`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 36.1×1
   - Lean: `private theorem not_mem_line_of_notCoplanar {x v u a b c : V3} (hcop : ¬ Coplanar ({x, a, b, c} : Set V3)) (hv : v ∈ ({a, b, c} : Set V3)...`
   - HOL: `#36.1`
5. **[M/NUM_SIGN] `lean/Kepler/Text/ConformingAuto4.lean:255` `affGt_triple_star`** ← `reference/flyspeck/text_formalization/jordan/float.hl:1553`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 36.1×1
   - Lean: `private theorem affGt_triple_star {x u v w y : V3} (hdisj : Disjoint ({x, u, v} : Set V3) {w}) (hy : y ∈ affGt ({x, u, v} : Set V3) {w}) ...`
   - HOL: `#36.1`
6. **[M/NUM_SIGN] `lean/Kepler/Text/ContraFan.lean:72` `two_h0`** ← `lean/scripts/packing/pack_defs.hl:147`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 1.26×1; 仅Lean: 2×1,2.52×1
   - Lean: `theorem two_h0 : (2 : ℝ) * h0 = 2.52`
   - HOL: `h0 = #1.26`
7. **[M/NUM_SIGN] `lean/Kepler/Text/ContraFanDeep.lean:57` `two_h0`** ← `lean/scripts/packing/pack_defs.hl:147`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 1.26×1; 仅Lean: 2×1,2.52×1
   - Lean: `private theorem two_h0 : (2 : ℝ) * h0 = 2.52`
   - HOL: `h0 = #1.26`
8. **[M/NUM_SIGN] `lean/Kepler/Text/ContraFanDeep.lean:3598` `cf4_etaP_box`** ← `reference/flyspeck/text_formalization/tame/Inequalities.hl:356`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 2×7,2.2×1; 仅Lean: 11×1,4×3,5×1,6.3504×3
   - Lean: `private theorem cf4_etaP_box (a b c : ℝ) (ha : a ∈ Icc (4:ℝ) 6.3504) (hb : b ∈ Icc (4:ℝ) 6.3504) (hc : c ∈ Icc (4:ℝ) 6.3504) : 0 ≤ (11 / ...`
   - HOL: `!y1 y2 y3. ineq[(&2, y1, &2 * h0); (&2, y2, &2 * h0); (&2, y3, &2 * h0)] (eta_y y1 y2 y3 pow 2 <= #2.2)`
9. **[M/NUM_SIGN] `lean/Kepler/Text/ContraFanDeep.lean:3697` `cf4_etaY_box`** ← `reference/flyspeck/text_formalization/tame/Inequalities.hl:356`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 2.2×1; 仅Lean: 11×1,5×1
   - Lean: `private theorem cf4_etaY_box (y1 y2 y3 : ℝ) (hy1 : y1 ∈ Icc (2:ℝ) (2 * h0)) (hy2 : y2 ∈ Icc (2:ℝ) (2 * h0)) (hy3 : y3 ∈ Icc (2:ℝ) (2 * h0...`
   - HOL: `!y1 y2 y3. ineq[(&2, y1, &2 * h0); (&2, y2, &2 * h0); (&2, y3, &2 * h0)] (eta_y y1 y2 y3 pow 2 <= #2.2)`
10. **[M/NUM_SIGN] `lean/Kepler/Text/EulerDerivCore.lean:117` `ea3_hD`** ← `reference/flyspeck/text_formalization/jordan/float.hl:1553`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 36.1×1; 仅Lean: -2×1,2×2
   - Lean: `private theorem ea3_hD (b c x : ℝ) : HasDerivAt (fun y : ℝ => ea3_D b c y) (-2 * x + (2 * b + 2 * c - b * c)) x`
   - HOL: `#36.1`
11. **[M/NUM_SIGN] `lean/Kepler/Text/EulerDerivCore.lean:124` `ea3_hsqrtD`** ← `reference/flyspeck/text_formalization/jordan/float.hl:1553`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 36.1×1; 仅Lean: -2×1,2×3
   - Lean: `private theorem ea3_hsqrtD (b c x : ℝ) (hd : ea3_D b c x ≠ 0) : HasDerivAt (fun y : ℝ => Real.sqrt (ea3_D b c y)) ((-2 * x + (2 * b + 2 *...`
   - HOL: `#36.1`
12. **[M/NUM_SIGN] `lean/Kepler/Text/EulerDerivCore.lean:131` `ea3_F`** ← `reference/flyspeck/text_formalization/jordan/float.hl:86`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 3×1; 仅Lean: -2×3,2×11,8×1
   - Lean: `fun y => -Real.pi / 2 - Real.arctan ((-2 * y + 2 * b + 2 * c - b * c) / (2 * Real.sqrt (ea3_D b c y))) - Real.arctan ((-2 * b + 2 * c + 2...`
   - HOL: `#3`
13. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAnchors.lean:53` `MainNonlinearTerminalV11`** ← `reference/flyspeck/text_formalization/local/terminal.hl:2239`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 200×1; 仅Lean: 3×2,4×1,5×1
   - Lean: `2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧ 2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧ 2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧ cstabAnchor ≤ y 3 ∧ y 3 ≤ 3.915 ∧ y 4 = 2 ∧ y 5 = 2`
   - HOL: `main_nonlinear_terminal_v11 ==> (!y1 y2 y3 y4 y5 y6. &2 <= y1 /\ y1 <= &2 * h0 /\ &2 <= y1 /\ y2 <= &2 * h0 /\ &2 <= y2 /\ y2 <= &2 * h0 ...`
14. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAnchors.lean:87` `scsTerminalEdgeEq2Anchor`** ← `reference/flyspeck/text_formalization/local/appendix.hl:1514`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 2×2,6×1
   - Lean: `theorem scsTerminalEdgeEq2Anchor (k p1 : ℕ) (v : ℕ → V3) (a b : ℕ → ℕ → ℝ) (J : ℕ → ℕ → Prop) (hy : ∀ y : Fin 6 → ℝ, MainNonlinearTermina...`
   - HOL: `main_nonlinear_terminal_v11 ==> (!s FF k p1 v. FF = IMAGE (\i. (v i,v (SUC i))) (:num) /\ is_scs_v39 s /\ k = scs_k_v39 s /\ 3 < k /\ MMs...`
15. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAnchors.lean:107` `scs4I2Imp4T1Anchor`** ← `reference/flyspeck/text_formalization/local/ARDBZYE.hl:1357`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 6×1
   - Lean: `theorem scs4I2Imp4T1Anchor (v : ℕ → V3) (hy : ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11 y) (hdiag : ∀ i j, scsDiag 4 i j → cstabAnchor < ...`
   - HOL: `main_nonlinear_terminal_v11 ==>(!v. v IN MMs_v39 scs_4I2 /\ (!i j. scs_diag 4 i j ==> cstab < dist(v i,v j)) ==> ~(MMs_v39 (scs_4T1)={}))`
16. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAnchors.lean:119` `scsSliceArrowAnchor`** ← `reference/flyspeck/text_formalization/local/appendix.hl:788`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 0.9×2,4×2
   - Lean: `theorem scsSliceArrowAnchor (d d' d'' bmq : ℝ) (k : ℕ) (hslice : d' < 0.9 ∧ d'' < 0.9 ∧ d ≤ d' + d'' ∧ bmq < 4 ∧ (k = 4 ∨ bmq ≤ cstabAnch...`
   - HOL: `scs_slice_v39 s p q d' d'' mkj = (scs_half_slice_v39 s p q d' mkj, scs_half_slice_v39 s q p d'' mkj)`
17. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto1.lean:641` `JEJTVGB_concl`** ← `reference/flyspeck/text_formalization/local/appendix.hl:180`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.467×1,2×2,3×1,4×1
   - Lean: `JEJTVGB_std_concl ∧ JEJTVGB_std3_concl ∧ JEJTVGB_pent_diag_concl ∧ JEJTVGB_pent_pro_concl ∧ JEJTVGB_quad_pro_concl ∧ JEJTVGB_quad_diag_concl`
   - HOL: `!V E FF. convex_local_fan (V,E,FF) /\ packing V /\ V SUBSET ball_annulus /\ CARD V = 4 /\ (!v w. ~(v = w) /\ v IN V /\ w IN V /\ ~({v,w} ...`
18. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto1.lean:824` `la1csAdj_diag6`** ← `reference/flyspeck/text_formalization/local/appendix.hl:455`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 6×10
   - Lean: `private theorem la1csAdj_diag6 {a1 a2 : ℝ} {i j x y : ℕ} (hxy : (x % 6 = i % 6 ∧ y % 6 = j % 6) ∨ (x % 6 = j % 6 ∧ y % 6 = i % 6)) (hd : ...`
   - HOL: `psort k (u:num#num) = (let i = FST u MOD k in let j = SND u MOD k in if (i <= j) then (i,j) else (j,i))`
19. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:192` `dartStd4_p11`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:1431`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.206×1,0.7573×1,1.433×1
   - Lean: `sorry`
   - HOL: `quad_nonlinear_v10 ==> (!y1 y2 y3 y4 y5 y6 y7 y8 y9. ineq (dart_std4 y1 y2 y3 y4 y5 y6 y7 y8 y9) ( tauq y1 y2 y3 y4 y5 y6 y7 y8 y9 < #0.2...`
20. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:210` `quadNonlinearV10`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:76`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 17×1
   - Lean: `∀ y1 y2 y3 y4 y5 y6 : ℝ, ∀ i : Fin 17, Q i y1 y2 y3 y4 y5 y6`
   - HOL: `quad_nonlinear_v10:bool`
21. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:214` `getQuadNonlinear_p11`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:76`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 17×2
   - Lean: `theorem getQuadNonlinear_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (h : quadNonlinearV10 Q) (i : Fin 17) (y1 y2 y3 y4 y5 y6 : ℝ) : ...`
   - HOL: `quad_nonlinear_v10:bool`
22. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:1004` `la11_arctan_eq_pi4_add`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:1407`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.945×1; 仅Lean: 4×1
   - Lean: `private theorem la11_arctan_eq_pi4_add {t : ℝ} (ht : 0 < t) : Real.arctan t = Real.pi / 4 + Real.arctan ((t - 1) / (t + 1))`
   - HOL: `atn (sqrt #1.914) < #0.945`
23. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:1211` `quad_4240815464_a_p11`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:1431`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 17×1
   - Lean: `theorem quad_4240815464_a_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hQ : quadNonlinearV10 Q) : ∀ y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ, i...`
   - HOL: `quad_nonlinear_v10 ==> (!y1 y2 y3 y4 y5 y6 y7 y8 y9. ineq (dart_std4 y1 y2 y3 y4 y5 y6 y7 y8 y9) ( tauq y1 y2 y3 y4 y5 y6 y7 y8 y9 < #0.2...`
24. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:1225` `quad_3862621143_revised_wlog_p11`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:1548`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 17×1
   - Lean: `theorem quad_3862621143_revised_wlog_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hQ : quadNonlinearV10 Q) : ∀ y0 y1 y2 y3 y5 y6 y7 y...`
   - HOL: `quad_nonlinear_v10 ==> (!y0 y1 y2 y3 y5 y6 y7 y8 y9. ineq [#3.01,y0,&4 * h0;#2.0,y1,&2 * h0; #2.0,y2,&2 * h0; #2.0,y3,&2 * h0; #2.0, y5, ...`
25. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto11.lean:1243` `quad_3862621143_revised_p11`** ← `reference/flyspeck/text_formalization/local/lp_details.hl:1732`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 17×1
   - Lean: `theorem quad_3862621143_revised_p11 {Q : Fin 17 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hQ : quadNonlinearV10 Q) : ∀ y0 y1 y2 y3 y5 y6 y7 y8 y9 ...`
   - HOL: `quad_nonlinear_v10 ==> (!y0 y1 y2 y3 y5 y6 y7 y8 y9. ineq [#3.01,y0,&4 * h0; #2.0,y1,&2 * h0; #2.0,y2,&2 * h0; #2.0, y3, &2 * h0; #2.0, y...`
26. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto18.lean:203` `mainNonlinearTerminalV11_p18`** ← `reference/flyspeck/text_formalization/local/terminal.hl:37`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 6×1
   - Lean: `∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p18 y`
   - HOL: `main_nonlinear_terminal_v11:bool`
27. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto18.lean:363` `SUM_NUMSEG4_p18`** ← `reference/flyspeck/text_formalization/local/IUNBUIG.hl:53`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅Lean: 5×1
   - Lean: `theorem SUM_NUMSEG4_p18 (t : ℕ → ℝ) : ∑ i ∈ Finset.range 5, t i = t 0 + t 1 + t 2 + t 3 + t 4`
   - HOL: `!t. sum (0..4) t = t 0 + t 1 + t 2 + t 3 + t 4`
28. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto19.lean:113` `mu6X_p19`** ← `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:401`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.01×1,0.012×1,0.07×1,2×1,2.52×2
   - Lean: `muY_p19 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)`
   - HOL: `mu_y y1 y2 y3 = (#0.012 + #0.07 * (#2.52 - y1) + #0.01 * (#2.52 * &2 - y2 - y3 ))`
29. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto19.lean:122` `taudP19`** ← `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:404`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.01×1,0.012×1,0.07×1,2×1,2.52×2
   - Lean: `flatTerm_p19 y1 + Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) * muY_p19 y1 y2 y3`
   - HOL: `(mu6_x:real->real->real->real->real->real->real) = (constant6 (#0.012) + constant6 (#0.07) * (constant6 (#2.52) - proj_y1) + constant6 (#...`
30. **[M/NUM_SIGN] `lean/Kepler/Text/LocalAuto19.lean:218` `taudD1numX_p19`** ← `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:457`
   - 为何可疑: 数值常量集合不等（0/1 已忽略）: 仅HOL: 0.52×1; 仅Lean: 2×2
   - Lean: `-0.07 * deltaX x1 x2 x3 x4 x5 x6 + (1 / 2) * mu6X_p19 x1 x2 x3 x4 x5 x6 * (deltaX1_p19 x1 x2 x3 x4 x5 x6 * 2 * Real.sqrt x1) + (sol0 / (2...`
   - HOL: `taud_D1_num_x = (let d = delta_x in let delta' = delta_x1 * (constant6 (&2)) * proj_y1 in let mu = mu6_x in let mu' = constant6 (-- #0.07...`

## 自检结果

`python3 lean/scripts/fidelity_check.py --selftest` — **PASS**（退出码 0）：
1. **SF-53 live（两处都必须抓到）**: `PackingAuto4.lean:197` `ccRealModelP4` 与 `:519` `CARD5_1074_LE_QYI` 均以 H/RANGE 抓到（HOL `0..cc_card_v11 cc - 1` vs Lean `Icc 0 (ccCardP4 cc)`），逐行定位准确。
2. **SF-49 重放**: 把 PA21:606 已修复的 `> -0.00569` 回置为历史误植 `> 0.00569` 后重扫，扫描器以 H/NUM_SIGN「同值反号: Lean `0.00569`×1 vs HOL `-0.00569`×1」抓到 `bank_BIXPCGW9455898160` ← ineq.hl:982。
3. **SF-49 live 状态**: HEAD 处该行已由 SF-49 修复为 `> -0.00569`（与 HOL 一致），扫描器正确不报；注意该行 docstring 自述「双重负号 = 0.00569」本身写反（`--` 是一元负号），属注释问题，建议另立一行注释小 SF。
4. 校准副产品: HEAD 全量扫描 H 级**恰好只有** SF-53 两处已知真误植，无其他 H。

## v2 建议

1. 把 `-- NEEDS …` 注记里的 `文件.hl:行` 指针全量解析并参与配对（v1 只用 docstring），可把配对率推到 ~90%+。
2. 常数比较引入「标识符↔HOL 定义体展开」一层：对 `aSpine5P4` 这类命名常数，追到其 `def` 体抽数字再比（消 `仅HOL/仅Lean` 噪声）。
3. RANGE 比较加入上界表达式规范化（`card` vs `cc_card_v11 cc` 词形映射），把「个数不等」降级为「形态评分」减少 M 噪声。
4. 对 `prove(N_concl)` 链式间接（`NHANH X` / `REWRITE_RULE[…] (ISPECL …)`）再走一层。
5. 输出 JSON 供编排者管道消费；增加 `--filter kind,sev,file`。

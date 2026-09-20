# P6-E: 155 定义闭包工单（ineqs_ast.json 根 → defs.json 传递闭包）

由 `lean/scripts/closure155.py` 生成（复现 kepler-g4e parse_defs.py 的
闭包游走；数据源只读）。每符号一行：

- class: resolved（defs.json 有体）/ primitive（内建实分析原语）/
  unsupported（parse_defs 无法解析的 HOL 体）/ missing（无定义）
- tier（Lean 侧现状）: A = 已有真体（项目原生/Mathlib）;
  B = 已按 B 档移植（camelCase + HOL 锚注释）; C = 桩（sorry/axiom）;
  D = 缺席
- batch: 批次号（1 = sqrtdelta 有理家族；2 = 6 元算子演算；
  N(enabler) = 批 N 依赖件）

| # | symbol | class | tier | Lean 侧 | batch | HOL source | 备注 |
|---|--------|-------|------|---------|-------|------------|------|
| 1 | `a_spine5` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:632 |  |
| 2 | `abc_of_quadratic` | resolved | B | abcOfQuadratic_p19 (lean/Kepler/Text/LocalAuto19.lean:160) |  | reference/flyspeck/text_formalization/general/sphere.hl:59 |  |
| 3 | `abs` | primitive | A | Mathlib |  |  |  |
| 4 | `acs` | primitive | A | Mathlib |  |  |  |
| 5 | `acs_sqrt_x1_d4` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:792 |  |
| 6 | `apex_A` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2985 |  |
| 7 | `apex_flat` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2888 |  |
| 8 | `apex_flat_h` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3711 |  |
| 9 | `apex_flat_hll` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3236 |  |
| 10 | `apex_flat_l` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3701 |  |
| 11 | `apex_std3_hll` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3343 |  |
| 12 | `apex_std3_lhh` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3903 |  |
| 13 | `apex_std3_lll_wxx` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3764 |  |
| 14 | `apex_std3_lll_xww` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3738 |  |
| 15 | `apex_sup_flat` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3103 |  |
| 16 | `arc_hhn` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:780 |  |
| 17 | `arclength` | resolved | B | arcLength (lean/Kepler/Text/PackingAuto18.lean:161) |  | reference/flyspeck/text_formalization/general/sphere.hl:258 |  |
| 18 | `arclength_x_123` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:798 |  |
| 19 | `arclength_y1` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:762 |  |
| 20 | `asn` | primitive | A | Mathlib |  |  |  |
| 21 | `asn797k` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:783 |  |
| 22 | `asnFnhk` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:786 |  |
| 23 | `atn` | primitive | A | Mathlib |  |  |  |
| 24 | `atn2` | resolved | B | atn2_p16 (lean/Kepler/Text/LocalAuto16.lean:269) |  | reference/flyspeck/text_formalization/general/sphere.hl:48 |  |
| 25 | `b_spine5` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:634 |  |
| 26 | `beta_bump_force_y` | resolved | B | betaBumpForceY (lean/Kepler/Text/IneqClosureDefs.lean:485) | 3 | reference/flyspeck/text_formalization/general/sphere.hl:614 |  |
| 27 | `beta_bump_lb` | resolved | B | betaBumpLb (lean/Kepler/Text/IneqClosureDefs.lean:493) | 3 | reference/flyspeck/text_formalization/general/sphere.hl:636 |  |
| 28 | `bump` | resolved | B | bump (lean/Kepler/Text/PackingAuto2.lean:487) |  | reference/flyspeck/text_formalization/general/sphere.hl:601 |  |
| 29 | `cayleyR` | resolved | D | - |  | auto:reference/flyspeck/text_formalization/leg/cayleyR_def.hl:32 |  |
| 30 | `compose6` | resolved | B | compose6 (lean/Kepler/Text/IneqClosureDefs.lean:284) | 2(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:72 | defs.json body_ast 是截断的 parse 残片（{"const":"f"}），以 nonlin_def.hl:72-80 原文为准 |
| 31 | `const1` | resolved | B | const1P19 (lean/Kepler/Text/LocalAuto19.lean:128) |  | reference/flyspeck/text_formalization/general/sphere.hl:197 |  |
| 32 | `constant6` | resolved | B | constant6 (lean/Kepler/Text/IneqClosureDefs.lean:274) | 2(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:249 |  |
| 33 | `cos` | primitive | A | Mathlib |  |  |  |
| 34 | `critical_edge_y` | resolved | B | criticalEdgeY (lean/Kepler/Text/PackingAuto2.lean:491) |  | reference/flyspeck/text_formalization/general/sphere.hl:603 |  |
| 35 | `dart4_diag3` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2866 |  |
| 36 | `dart4_diag3_b` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2591 |  |
| 37 | `dartX` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2828 |  |
| 38 | `dartY` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2847 |  |
| 39 | `dart_mll_n` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3373 |  |
| 40 | `dart_mll_w` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3363 |  |
| 41 | `dart_std3` | unsupported | B | dartStd3 (lean/Kepler/Text/IneqClosureDefs.lean:561) | 5(enabler) | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:2697 | define_dart 列表域（parse_defs triage unsupported）；List (ℝ×ℝ×ℝ) 直接可移植，批 5 落地 |
| 42 | `dart_std3_big` | resolved | B | dartStd3Big (lean/Kepler/Text/IneqClosureDefs.lean:568) | 5 | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3079 | = dart_std3 verbatim（ineq.hl:3079，'same domain but extra disjunct'） |
| 43 | `dart_std3_big_200_218` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3256 |  |
| 44 | `dart_std3_lw` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3552 |  |
| 45 | `dart_std3_mini` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3191 |  |
| 46 | `dart_std3_small` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:3046 |  |
| 47 | `dart_std4` | unsupported | D | - |  | auto:reference/flyspeck/text_formalization/nonlinear/ineq.hl:1863 |  |
| 48 | `delta4_squared_x` | resolved | B | delta4SquaredX (lean/Kepler/Text/IneqClosureDefs.lean:209) | 1 | reference/flyspeck/text_formalization/general/sphere.hl:835 |  |
| 49 | `delta4_squared_y` | resolved | B | delta4SquaredY_p11 (lean/Kepler/Text/LocalAuto11.lean:198) |  | reference/flyspeck/text_formalization/general/sphere.hl:838 |  |
| 50 | `delta4_y` | resolved | B | delta4Y_p11 (lean/Kepler/Text/LocalAuto11.lean:188) |  | reference/flyspeck/text_formalization/general/sphere.hl:543 |  |
| 51 | `delta_234_x` | resolved | B | delta234X_p11 (lean/Kepler/Text/LocalAuto11.lean:184) |  | reference/flyspeck/text_formalization/general/sphere.hl:848 |  |
| 52 | `delta_x` | resolved | B | deltaXf_p16 (lean/Kepler/Text/LocalAuto16.lean:276) |  | reference/flyspeck/text_formalization/general/sphere.hl:86 |  |
| 53 | `delta_x1` | resolved | B | deltaX1f_p11 (lean/Kepler/Text/LocalAuto11.lean:159) |  | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:418 |  |
| 54 | `delta_x4` | resolved | B | deltaX4 (lean/Kepler/Text/LocalAuto1.lean:766) |  | reference/flyspeck/text_formalization/general/sphere.hl:110 |  |
| 55 | `delta_y` | resolved | B | deltaY_p11 (lean/Kepler/Text/LocalAuto11.lean:149) |  | reference/flyspeck/text_formalization/general/sphere.hl:92 |  |
| 56 | `dih2_y` | resolved | B | dih2Y (lean/Kepler/Text/IneqClosureDefs.lean:522) | 5 | reference/flyspeck/text_formalization/general/sphere.hl:163 |  |
| 57 | `dih3_y` | resolved | B | dih3Y (lean/Kepler/Text/IneqClosureDefs.lean:526) | 5 | reference/flyspeck/text_formalization/general/sphere.hl:166 |  |
| 58 | `dih4_x_div_sqrtdelta_posbranch` | resolved | B | dih4XDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:127) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:163 |  |
| 59 | `dih_x` | resolved | B | dihXf_p16 (lean/Kepler/Text/LocalAuto16.lean:288) |  | reference/flyspeck/text_formalization/general/sphere.hl:153 |  |
| 60 | `dih_x_div_sqrtdelta_posbranch` | resolved | B | dihXDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:95) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:138 |  |
| 61 | `dih_y` | resolved | B | dihY_p16 (lean/Kepler/Text/LocalAuto16.lean:294) |  | reference/flyspeck/text_formalization/general/sphere.hl:159 |  |
| 62 | `dummy6` | resolved | B | dummy6 (lean/Kepler/Text/IneqClosureDefs.lean:372) | 3(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:263 |  |
| 63 | `enclosed` | resolved | D | - |  | auto:reference/flyspeck/text_formalization/leg/enclosed_def.hl:22 |  |
| 64 | `eta_x` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:127 |  |
| 65 | `eta_y` | resolved | C | eta_y (lean/Kepler/Text/PackingAuto21.lean:177) |  | reference/flyspeck/text_formalization/general/sphere.hl:131 |  |
| 66 | `eulerA_x` | resolved | B | eulerAx_p19 (lean/Kepler/Text/LocalAuto19.lean:227) |  | reference/flyspeck/text_formalization/general/sphere.hl:831 |  |
| 67 | `gamma23_full8_x` | resolved | B | gamma23Full8X (lean/Kepler/Text/IneqClosureDefs.lean:459) | 3 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:383 |  |
| 68 | `gamma23_keep135_x` | resolved | B | gamma23Keep135X (lean/Kepler/Text/IneqClosureDefs.lean:465) | 3 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:390 |  |
| 69 | `gamma2_x1_div_a_v2` | resolved | B | gamma2X1DivAV2 (lean/Kepler/Text/IneqClosureDefs.lean:413) | 3 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:346 |  |
| 70 | `gamma2_x_div_azim_v2` | resolved | B | gamma2XDivAzimV2 (lean/Kepler/Text/IneqClosureDefs.lean:407) | 3(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:341 | PA21:164 已有同名 verbatim 体；同上 atn2 冲突不可复用，批 3 立 canonical gamma2XDivAzimV2 |
| 71 | `gamma3_x` | resolved | B | gamma3X (lean/Kepler/Text/IneqClosureDefs.lean:433) | 3 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:380 |  |
| 72 | `gamma3f` | resolved | B | gamma3f (lean/Kepler/Text/PackingAuto20.lean:138) |  | reference/flyspeck/text_formalization/general/sphere.hl:582 |  |
| 73 | `gamma3f_x_div_sqrtdelta` | resolved | B | gamma3fXDivSqrtdelta (lean/Kepler/Text/IneqClosureDefs.lean:441) | 3 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:349 |  |
| 74 | `gamma4f` | resolved | B | gamma4fgcy (lean/Kepler/Text/PackingAuto20.lean:122) |  | reference/flyspeck/text_formalization/general/sphere.hl:563 |  |
| 75 | `gamma4fgcy` | resolved | B | gamma4fgcyP25 (lean/Kepler/Text/PackingAuto25.lean:119) |  | reference/flyspeck/text_formalization/general/sphere.hl:566 |  |
| 76 | `h0` | resolved | B | h0 (lean/Kepler/Text/PackingAuto2.lean:458) |  | reference/flyspeck/text_formalization/general/sphere.hl:203 |  |
| 77 | `h0cut` | resolved | B | h0cut (lean/Kepler/Text/PackingAuto21.lean:182) |  | reference/flyspeck/text_formalization/general/sphere.hl:517 |  |
| 78 | `hminus` | resolved | B | hminus (lean/Kepler/Text/PackingAuto2.lean:468) |  | reference/flyspeck/text_formalization/general/sphere.hl:529 |  |
| 79 | `hplus` | resolved | B | hplus (lean/Kepler/Text/PackingAuto2.lean:431) |  | reference/flyspeck/text_formalization/general/sphere.hl:515 |  |
| 80 | `interp` | resolved | B | interp_p2 (lean/Kepler/Text/LocalAuto2.lean:325) |  | reference/flyspeck/text_formalization/general/sphere.hl:195 |  |
| 81 | `ldih2_x_div_sqrtdelta_posbranch` | resolved | B | ldih2XDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:150) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:148 |  |
| 82 | `ldih3_x_div_sqrtdelta_posbranch` | resolved | B | ldih3XDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:154) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:151 |  |
| 83 | `ldih5_x_div_sqrtdelta_posbranch` | resolved | B | ldih5XDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:158) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:154 |  |
| 84 | `ldih6_x_div_sqrtdelta_posbranch` | resolved | B | ldih6XDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:162) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:157 |  |
| 85 | `ldih_x_div_sqrtdelta_posbranch` | resolved | B | ldihXDivSqrtdeltaPosbranch (lean/Kepler/Text/IneqClosureDefs.lean:136) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:144 |  |
| 86 | `lfun` | resolved | B | lfun (lean/Kepler/Text/PackingAuto2.lean:461) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:525 |  |
| 87 | `lfun_y1` | resolved | B | lfunY1 (lean/Kepler/Text/IneqClosureDefs.lean:536) | 5 | reference/flyspeck/text_formalization/general/sphere.hl:789 |  |
| 88 | `lmfun` | resolved | B | lmfun (lean/Kepler/Text/PackingAuto2.lean:464) |  | reference/flyspeck/text_formalization/general/sphere.hl:523 |  |
| 89 | `lnazim` | resolved | B | lnazimP19 (lean/Kepler/Text/LocalAuto19.lean:131) |  | reference/flyspeck/text_formalization/general/sphere.hl:213 |  |
| 90 | `log` | primitive | A | Mathlib |  |  |  |
| 91 | `ly` | resolved | B | lyP19 (lean/Kepler/Text/LocalAuto19.lean:124) |  | reference/flyspeck/text_formalization/general/sphere.hl:199 |  |
| 92 | `marchal_quartic` | resolved | B | marchalQuartic (lean/Kepler/Text/PackingAuto2.lean:435) |  | reference/flyspeck/text_formalization/general/sphere.hl:519 |  |
| 93 | `matan` | resolved | B | matan (lean/Kepler/Text/IneqClosureDefs.lean:31) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:728 | 批 5 名单，批 1 已作为 enabler 落地 |
| 94 | `mk_126` | resolved | B | mk126 (lean/Kepler/Text/IneqClosureDefs.lean:290) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:267 |  |
| 95 | `mk_135` | resolved | B | mk135 (lean/Kepler/Text/IneqClosureDefs.lean:298) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:273 |  |
| 96 | `mk_456` | resolved | B | mk456 (lean/Kepler/Text/IneqClosureDefs.lean:294) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:270 |  |
| 97 | `mm1` | resolved | B | mm1 (lean/Kepler/Text/PackingAuto2.lean:425) |  | reference/flyspeck/text_formalization/general/sphere.hl:511 |  |
| 98 | `mm2` | resolved | B | mm2 (lean/Kepler/Text/PackingAuto2.lean:428) |  | reference/flyspeck/text_formalization/general/sphere.hl:513 |  |
| 99 | `muR` | resolved | B | muRP38 (lean/Kepler/Text/LocalAuto38.lean:151) |  | auto:reference/flyspeck/text_formalization/leg/muR_def.hl:40 |  |
| 100 | `node2_y` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:222 |  |
| 101 | `norm2hh` | resolved | B | norm2hh (lean/Kepler/Text/IneqClosureDefs.lean:335) | 2 | reference/flyspeck/text_formalization/general/sphere.hl:597 | 复用 PackingAuto2 的 hminus（Classical.epsilon 版）/hplus |
| 102 | `pi` | primitive | A | Mathlib |  |  |  |
| 103 | `proj_x1` | resolved | B | projX1 (lean/Kepler/Text/IneqClosureDefs.lean:233) | 2(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:40 | HOL 多态；Lean 只移植闭包用到的 ℝ⁶→ℝ 实例 |
| 104 | `proj_x2` | resolved | B | projX2 (lean/Kepler/Text/IneqClosureDefs.lean:236) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:42 | HOL 多态；同上 |
| 105 | `proj_x3` | resolved | B | projX3 (lean/Kepler/Text/IneqClosureDefs.lean:239) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:44 | HOL 多态；同上 |
| 106 | `proj_x4` | resolved | B | projX4 (lean/Kepler/Text/IneqClosureDefs.lean:242) | 2(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:46 | HOL 多态；同上 |
| 107 | `proj_x5` | resolved | B | projX5 (lean/Kepler/Text/IneqClosureDefs.lean:245) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:48 | HOL 多态；同上 |
| 108 | `proj_x6` | resolved | B | projX6 (lean/Kepler/Text/IneqClosureDefs.lean:248) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:50 | HOL 多态；同上 |
| 109 | `proj_y4` | resolved | B | projY4 (lean/Kepler/Text/IneqClosureDefs.lean:256) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:300 |  |
| 110 | `proj_y5` | resolved | B | projY5 (lean/Kepler/Text/IneqClosureDefs.lean:259) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:303 |  |
| 111 | `proj_y6` | resolved | B | projY6 (lean/Kepler/Text/IneqClosureDefs.lean:262) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:306 |  |
| 112 | `promote1_to_6` | resolved | B | promote1To6 (lean/Kepler/Text/IneqClosureDefs.lean:310) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:254 |  |
| 113 | `promote3_to_6` | resolved | B | promote3To6 (lean/Kepler/Text/IneqClosureDefs.lean:313) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:251 |  |
| 114 | `quadratic_root_plus` | resolved | B | quadraticRootPlus_p11 (lean/Kepler/Text/LocalAuto11.lean:154) |  | reference/flyspeck/text_formalization/general/sphere.hl:67 |  |
| 115 | `rad2_x` | resolved | C | rad2XP25 (lean/Kepler/Text/PackingAuto25.lean:89) |  | reference/flyspeck/text_formalization/general/sphere.hl:271 |  |
| 116 | `rad2_y` | resolved | B | rad2YP25 (lean/Kepler/Text/PackingAuto25.lean:93) |  | reference/flyspeck/text_formalization/general/sphere.hl:541 |  |
| 117 | `rhazim` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:211 |  |
| 118 | `rhazim2` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:226 |  |
| 119 | `rho` | resolved | B | rho_p2 (lean/Kepler/Text/LocalAuto2.lean:336) |  | reference/flyspeck/text_formalization/general/sphere.hl:201 |  |
| 120 | `rho_x` | resolved | B | rhoX (lean/Kepler/Text/IneqClosureDefs.lean:542) | 5 | reference/flyspeck/text_formalization/general/sphere.hl:137 |  |
| 121 | `rotate2` | resolved | B | rotate2 (lean/Kepler/Text/IneqClosureDefs.lean:62) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:654 |  |
| 122 | `rotate3` | resolved | B | rotate3 (lean/Kepler/Text/IneqClosureDefs.lean:66) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:657 |  |
| 123 | `rotate4` | resolved | B | rotate4 (lean/Kepler/Text/IneqClosureDefs.lean:70) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:660 |  |
| 124 | `rotate5` | resolved | B | rotate5 (lean/Kepler/Text/IneqClosureDefs.lean:74) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:663 |  |
| 125 | `rotate6` | resolved | B | rotate6 (lean/Kepler/Text/IneqClosureDefs.lean:78) | 1(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:666 |  |
| 126 | `scalar6` | resolved | B | scalar6 (lean/Kepler/Text/IneqClosureDefs.lean:326) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:279 |  |
| 127 | `sin` | primitive | A | Mathlib |  |  |  |
| 128 | `sol0` | resolved | B | sol0 (lean/Kepler/Text/PackingAuto2.lean:419) |  | reference/flyspeck/text_formalization/general/sphere.hl:207 |  |
| 129 | `sol_euler156_x_div_sqrtdelta` | resolved | B | solEuler156XDivSqrtdelta (lean/Kepler/Text/IneqClosureDefs.lean:201) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:127 |  |
| 130 | `sol_euler246_x_div_sqrtdelta` | resolved | B | solEuler246XDivSqrtdelta (lean/Kepler/Text/IneqClosureDefs.lean:191) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:121 |  |
| 131 | `sol_euler345_x_div_sqrtdelta` | resolved | B | solEuler345XDivSqrtdelta (lean/Kepler/Text/IneqClosureDefs.lean:196) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:124 |  |
| 132 | `sol_euler_x_div_sqrtdelta` | resolved | B | solEulerXDivSqrtdelta (lean/Kepler/Text/IneqClosureDefs.lean:173) | 1 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:115 |  |
| 133 | `sol_x` | resolved | B | solX (lean/Kepler/Text/IneqClosureDefs.lean:379) | 3(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:181 | LocalAuto38:75 有 sorry 桩 solXP38（锚注释形式不同，扫描漏检）；批 3 在 IneqClosureDefs 立真体 solX |
| 134 | `sol_y` | resolved | B | solY_p19 (lean/Kepler/Text/LocalAuto19.lean:119) |  | reference/flyspeck/text_formalization/general/sphere.hl:185 |  |
| 135 | `sqrt` | primitive | A | Mathlib |  |  |  |
| 136 | `sqrt2` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:76 |  |
| 137 | `sqrt3` | resolved | B | sqrt3 (lean/Kepler/Text/PackingAuto22.lean:112) |  | reference/flyspeck/text_formalization/general/sphere.hl:77 |  |
| 138 | `sqrt8` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:75 |  |
| 139 | `tame_table_d` | resolved | B | tameTableD (lean/Kepler/Text/IneqClosureDefs.lean:510) | 5 | reference/flyspeck/text_formalization/general/sphere.hl:803 | ℕ 参数表常数；分支内 &r/&s 为 ℕ→ℝ cast，guard 在 ℕ 层 |
| 140 | `tau0` | resolved | B | tau0 (lean/Kepler/Text/PackingAuto2.lean:422) |  | reference/flyspeck/text_formalization/general/sphere.hl:509 |  |
| 141 | `taum` | resolved | B | taumP19 (lean/Kepler/Text/LocalAuto19.lean:135) |  | reference/flyspeck/text_formalization/general/sphere.hl:215 |  |
| 142 | `tauq` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:244 |  |
| 143 | `two6` | resolved | B | two6 (lean/Kepler/Text/IneqClosureDefs.lean:277) | 2 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:259 |  |
| 144 | `uni` | resolved | B | uni (lean/Kepler/Text/IneqClosureDefs.lean:365) | 3(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:246 | defs.json body_ast 截断（(f:A->B) 类型标注触发 parse bug）；HOL (f,x) 对在 Lean 解柯里化为 uni f x |
| 145 | `ups_126` | resolved | B | ups126 (lean/Kepler/Text/IneqClosureDefs.lean:550) | 5 | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:446 |  |
| 146 | `ups_x` | resolved | B | upsX_p11 (lean/Kepler/Text/LocalAuto11.lean:144) |  | reference/flyspeck/text_formalization/general/sphere.hl:122 |  |
| 147 | `vol3f` | resolved | B | vol3f (lean/Kepler/Text/PackingAuto20.lean:129) |  | reference/flyspeck/text_formalization/general/sphere.hl:573 |  |
| 148 | `vol3f_456` | resolved | B | vol3f456 (lean/Kepler/Text/IneqClosureDefs.lean:423) | 3(enabler) | reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:365 | 原批 5 名单，作为 gamma3_x 依赖随批 3 提前落地 |
| 149 | `vol3r` | resolved | B | vol3r (lean/Kepler/Text/PackingAuto20.lean:126) |  | reference/flyspeck/text_formalization/general/sphere.hl:571 |  |
| 150 | `vol4f` | resolved | B | vol4f (lean/Kepler/Text/PackingAuto20.lean:107) |  | reference/flyspeck/text_formalization/general/sphere.hl:549 |  |
| 151 | `vol_x` | resolved | B | volX (lean/Kepler/Text/IneqClosureDefs.lean:390) | 3(enabler) | reference/flyspeck/text_formalization/general/sphere.hl:251 | PA20:99 volXf 为 verbatim 孪生，但 PA20 与 SphereKit 的 atn2 同名冲突使其不可跨 import 复用；批 3 立 canonical volX |
| 152 | `vol_y` | resolved | B | volY (lean/Kepler/Text/PackingAuto20.lean:103) |  | reference/flyspeck/text_formalization/general/sphere.hl:547 |  |
| 153 | `x1_delta_x` | resolved | D | - |  | reference/flyspeck/text_formalization/general/sphere.hl:840 |  |
| 154 | `x1_delta_y` | resolved | B | x1DeltaY_p11 (lean/Kepler/Text/LocalAuto11.lean:193) |  | reference/flyspeck/text_formalization/general/sphere.hl:842 |  |
| 155 | `y_of_x` | resolved | B | yOfX_p11 (lean/Kepler/Text/LocalAuto11.lean:177) |  | reference/flyspeck/text_formalization/general/sphere.hl:538 |  |

closure stats: roots=87 size=155 resolved=124 primitives=9 unsupported=22 missing=0; statement variables excluded: x1, x2, x3, x4, x5, x6, y1, y2, y3, y4, y5, y6, y7, y8, y9
resolved-by-tier: B=104, C=2, D=18

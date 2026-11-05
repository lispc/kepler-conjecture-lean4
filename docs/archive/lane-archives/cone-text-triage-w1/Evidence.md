# Evidence — 原始机器证据

所有 `grep`/`sed` 均在 `/Users/zhangzhuo/repos/kepler-conjecture-lean4` 工作树（读时 HEAD `b49461bb`，任务书基线 `8a91eaaa`）执行；未改任何文件。

---

## 0. 探针（唯一一次编译；standalone，禁 lake）

命令：

```bash
cd /tmp/cone-text-triage-w1
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q /tmp/cone-text-triage-w1/probe1.log lean /tmp/cone-text-triage-w1/probe1.lean
echo "RC=$?"
```

RC = **1**（唯一错误是 `fully_surrounded_perimeter_bound` 未加 `Kepler.Text.TameLp` 命名空间前缀；其余 20 条 `#print axioms` 全部正常打印，结论不受影响）。日志原文：

```
'Kepler.Text.tiny_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TFITSKC_p27' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.JCYFMRP_p27' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.RRCWNSJ_p26' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.NUXCOEAv2_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_6I1_BERAK_BY_CSTAB' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.LFLACKU_p23' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.OCBICBY_p22' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_5M2_IMP_SCS_5T1_p29' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.UAGHHBM_p30' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.general_482_deformation_p21' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.VPWSHTO_p15' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.URRPHBZ2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
/tmp/cone-text-triage-w1/probe1.lean:34:14: error(lean.unknownIdentifier): Unknown constant `fully_surrounded_perimeter_bound`
'Kepler.Text.MM_4I2_IMP_4T2_4T1_p33' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I1_IMP_SCS_4I2_p33' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_IMP_SCS_4T1_p33' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.NWDGKXH_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YOBIMPP_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.MIQMCSN_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**结论 A**：`tiny_probe (_h : main_nonlinear_terminal_v11) : True := trivial` 无 sorryAx ⇒ mnt11 已不是常量级污染（`docs/axiom-ledger.md` §2.3a 过时）。
**结论 B**：`NUXCOEAv2_p28` 已是标准三 ⇒ TSV 行过时（`ad7e9dba` 闭合）。
**结论 C**：其余 18 条实测含 sorryAx（TSV 行仍有效，但原因是具体依赖/本体 sorry，不是 mnt11）。

---

## 1. mnt11 物化证据

```
$ rg -n 'main_nonlinear_terminal_v11' lean/Kepler/Text/LocalAuto1.lean | head
2134:/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:24-44): the closed
2139:def main_nonlinear_terminal_v11 : Prop :=
2143:theorem get_main_nonlinear_of_mem {id : String} (h : main_nonlinear_terminal_v11)
2151:theorem main_nonlinear_terminal_v11_4717061266 (h : main_nonlinear_terminal_v11) :

$ sed -n '2139,2141p' lean/Kepler/Text/LocalAuto1.lean
def main_nonlinear_terminal_v11 : Prop :=
  ∀ id ∈ mainNonlinearTerminalV11Ids_t11, get_main_nonlinear id

$ sed -n '1894,1897p' lean/Kepler/Text/LocalAuto1.lean
noncomputable def mainEstimate_4717061266 : Prop :=
  ∀ y1 y2 y3 y4 y5 y6 : ℝ,
    (2 : ℝ) ≤ y1 → y1 ≤ (2 : ℝ)*h0 → ... →
    deltaY y1 y2 y3 y4 y5 y6 > (0 : ℝ)
```

（`get_main_nonlinear` 是 `match id with | "…" => mainEstimate_… | _ => True` 的纯定义，`LocalAuto1.lean:2090-2132`。）

`p21` 同理是干净定义（`LocalAuto21.lean:130`）：

```
def MainNonlinearTerminalV11_p21 (y : Fin 6 → ℝ) : Prop :=
  2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧ … ∧ y 4 = 2 ∧ y 5 = 2
```

真正剩余的银行锚（装配层）：`lean/Kepler/Text/LocalConcl.lean:1988 private theorem mnt11_anchor : main_nonlinear_terminal_v11 := sorry`、`:1994 private theorem p21_anchor : mainNonlinearTerminalV11_p21 := sorry`。

---

## 2. `general_482_deformation_p21` 根（卡 5 条）

```
$ sed -n '1178,1200p' lean/Kepler/Text/LocalAuto21.lean
theorem general_482_deformation_p21 (h : mainNonlinearTerminalV11_p21)
    (s : ScsV39) (FF : Set (V3 × V3)) (k p0 p1 p2 : ℕ) (v : ℕ → V3)
    ...
    dist (v p1) (v p2) = 2 := by
  -- DISCHARGES: HOL `general_482_deformation` (640 lines): ...
  sorry
```

递归闭包（`python3 -I roots.py general_482_deformation_p21`）：

```
=== general_482_deformation_p21: 1 sorry-reachable decls
   d0 general_482_deformation_p21  Text/LocalAuto21.lean:1178
=== CUXVZOZ_p21: 1 sorry-reachable decls
   d1 general_482_deformation_p21  Text/LocalAuto21.lean:1178
```

`general_482` 的 7 条前置（全部 `sorry`，声明行实测）：

```
+ deform_simplex_decrease_edge23_p21: Text/LocalAuto21.lean:276 sorry=True
+ deform_simplex_684_pent_p21:       Text/LocalAuto21.lean:328 sorry=True
+ deform_planar_p21:                 Text/LocalAuto21.lean:440 sorry=True
+ deform_planar_second_version_p21:  Text/LocalAuto21.lean:485 sorry=True
+ deformation_BBs_p21:               Text/LocalAuto21.lean:859 sorry=True
+ deformation_BBs_ALT_p21:           Text/LocalAuto21.lean:883 sorry=True
+ tau3_azim_p21:                     Text/LocalAuto21.lean:1164 sorry=True
```

`JCYFMRP_p27` / `TFITSKC_p27` 的 NEEDS 原文：

```
$ sed -n '495,515p' lean/Kepler/Text/LocalAuto27.lean
theorem JCYFMRP_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3), ...
                ∃ i, dist (v i) (v (i + 1)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS `CUXVZOZ` (the linear loop reaching the boundary)
    -- composed with the `SCS_M_LE_1` pinned-edge lemma.

$ sed -n '331,345p' lean/Kepler/Text/LocalAuto27.lean
theorem TFITSKC_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), ...
                  dist (v (i + 1)) (v (i + 2)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS `TFITSKCv1`; the `i'` J-emptyness premise is derived
```

`TFITSKCv1_p27` 自身（`LocalAuto27.lean:311`，`sorry`）的 NEEDS 与 `docs/priority-queue.md:171` 的 BLOCKED 判定一致（`CUXVZOZ`/`CJBDXXN` + `Polar_fan.GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` = LocalAuto7:954）。

---

## 3. LA33 链（3 条）

```
$ grep -n 'theorem SCS_4I2_STRAIGHT_p33\|theorem SCS_4I2_STRAIGHT_ALL_p33\|theorem MM_4I2_IMP_4T2_4T1_p33\|theorem SCS_4I1_IMP_SCS_4I2_p33\|theorem SCS_4I2_IMP_SCS_4T1_p33' lean/Kepler/Text/LocalAuto33.lean
2059:theorem SCS_4I2_STRAIGHT_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i : ℕ)
2065:theorem SCS_4I2_STRAIGHT_ALL_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
2126:theorem MM_4I2_IMP_4T2_4T1_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
2163:theorem SCS_4I1_IMP_SCS_4I2_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
1803:theorem SCS_4I2_IMP_SCS_4T1_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
```

`SCS_4I2_IMP_SCS_4T1_p33` 的 HOL 证明体（`reference/flyspeck/text_formalization/local/ARDBZYE.hl:1357-1439`）实际调用：

```
THEN MRESA_TAC Nuxcoea.MMS_IMP_BBS[`scs_4I2`;`v`]
THEN MP_TAC Rrcwnsj.RRCWNSJ
THEN MP_TAC JCYFMRP_V3
THEN MP_TAC Jlxfdmj.JLXFDMJ
THEN MP_TAC (GEN_ALL Ppbtydq.XWNHLMD_MM)
```

对应 Lean 状态：

```
+ RRCWNSJ_p26:        Text/LocalAuto26.lean:829  sorry=True
+ JCYFMRP_V3_p29:     Text/LocalAuto29.lean:3601 sorry=True
+ JLXFDMJ_p27:        Text/LocalAuto27.lean:559  sorry=True
+ XWNHLMD_MM_p33:     Text/LocalAuto33.lean:527  sorry=False
+ MMS_IMP_BBS_p28:    Text/LocalAuto28.lean:194  sorry=False
```

`MM_4I2_IMP_4T2_4T1_p33` 的前置（HOL `:2339-2514` 实引）：

```
+ ASSUME_MIN_DIAG_p33:        LocalAuto33.lean:1930 sorry=False
+ SCS_4I2_3_LE_A_p33:         LocalAuto33.lean:1957 sorry=False
+ SCS_4I2_STRAIGHT_ALL_p33:   LocalAuto33.lean:2065 sorry=True   ← 唯一红点
+ DIST_DIAG_2_CASES_EQ_3_p33: LocalAuto33.lean:1900 sorry=False
+ SCS_DIAG_ADD1_p33:          LocalAuto33.lean:1922 sorry=False
+ BB_VV_FUN_EQ_p26:           LocalAuto26.lean:198  sorry=False
+ XWNHLMD_MM_p33:             LocalAuto33.lean:527  sorry=False
```

---

## 4. LA32 三条（4M6/4M7/4M8 箭头塔）

```
$ sed -n '993,1030p' lean/Kepler/Text/LocalAuto32.lean
theorem EXTREMAL_SCS_4M6_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M6' → ...
  sorry
  -- NEEDS: main_nonlinear_terminal_v11 + MMS_IMP_BBS + BB_VV_FUN_EQ
  -- + SCS_4M6_STAND_OR_PRO_p32 + VASYYAU (str case split).
...
theorem SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 : ... := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + EXTREMAL_SCS_4M6_p32 (dist on
  -- diagonals) + STAB_MOD/YRTAFYH kit on the stab branch.

$ sed -n '1030,1036p' lean/Kepler/Text/LocalAuto32.lean
theorem NWDGKXH_p32 :
    main_nonlinear_terminal_v11 → scsArrowV39 {scs4M6'} {scs4T3, scs4T5} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via ({scs_4T3} ∪ stab-diag set) +
  -- SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 + hexagons arrow
  -- stab-diag-of-4M6 → {scs_4T3, scs_4T5}.
```

EXTREMAL 的前置全绿：

```
+ MMS_IMP_BBS_p28:            LocalAuto28.lean:194  sorry=False
+ BB_VV_FUN_EQ_p26:           LocalAuto26.lean:198  sorry=False
+ SCS_4M6_STAND_OR_PRO_p32:   LocalAuto32.lean:960  sorry=False
+ VASYYAU_p25:                LocalAuto25.lean:2541 sorry=False
+ STAB_MOD:                   LocalAuto20.lean:1655 sorry=False
+ YRTAFYH_p17:                LocalAuto17.lean:1129 sorry=False
+ SET_STAB_4M6_ARROW_4T5_p33: LocalAuto33.lean:4298 sorry=False
```

4M7/4M8 塔的红点：

```
+ SCS_4M7_ARROW_STAB_4M7_4M6_p32:      LocalAuto32.lean:1162 sorry=True
+ STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32:  LocalAuto32.lean:680  sorry=True
+ SCS_4M7_SLICE_13_ARROW_3T4_p32:      LocalAuto32.lean:657  sorry=True
+ SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32:  LocalAuto32.lean:673  sorry=True
+ SCS_4M8_ARROW_STEP_ONE_p32:          LocalAuto32.lean:1419 sorry=True
+ SET_STAB_4M8_ARROW_3T4_p32:          LocalAuto32.lean:896  sorry=True
+ SCS_4M8_02_ARROW_3T7_p32:            LocalAuto32.lean:1569 sorry=True
+ SCS_4M8_SLICE_13_ARROW_3T4_p32:      LocalAuto32.lean:882  sorry=True
+ SCS_4M8_SLICE_02_ARROW_3T4_p32:      LocalAuto32.lean:889  sorry=True
+ YXIONXL2_concl:                      LocalAuto1.lean:2578  sorry=True
```

（`SCS_OPP_REFL` 有已证孪生 `SCS_OPP_REFL_fb`，`FanBaseKit.lean:3135`，可替代 `SCS_OPP_REFL_p13`（LocalAuto13:1792，sorry）。）

---

## 5. RRCWNSJ_p26（唯一 CLEAN 的 M）

```
$ sed -n '827,840p' lean/Kepler/Text/LocalAuto26.lean
/-- HOL `RRCWNSJ` (RRCWNSJ.hl:248). Proof pending (needs
`MMS_IMP_BBPRIME` / `JKQEWGV2` / `BBS_IMP_CONVEX_LOCAL_FAN`). -/
theorem RRCWNSJ_p26 :
    main_nonlinear_terminal_v11 →
      ∀ s : ScsV39, ∀ v : ℕ → V3, ...
        (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v := by
  sorry
```

递归闭包（0 sorry）：

```
=== MMS_IMP_BBPRIME_p28: 0 sorry-reachable decls
=== JKQEWGV2_p23: 0 sorry-reachable decls
=== BBS_IMP_CONVEX_LOCAL_FAN_p34: 0 sorry-reachable decls
```

风险证据（HOL `RRCWNSJ.hl:248-872` 实引，NEEDS 未列）：

```
THEN MP_TAC Wrgcvdr_cizmrrh.CIZMRRH          → CIZMRRH (LocalAuto3:2734) proved
THEN MP_TAC Local_lemmas.CVLF_LF_F           → CVLF_LF_F (LocalAuto5:6740) proved
THEN MRESA_TAC LUNAR_IN_V[...]               → LUNAR_IN_V_p26 (LocalAuto26:224) proved
THEN MRESA_TAC Axjrpnc.AXJRPNC[...]          → AXJRPNC_p26 (LocalAuto26:1307) proved
THEN MP_TAC JCYFMRP_V3                       → JCYFMRP_V3_p29 (LocalAuto29:3601) SORRY
THEN MP_TAC Jlxfdmj.JLXFDMJ                  → JLXFDMJ_p27 (LocalAuto27:559) SORRY
```

---

## 6. MISSING 证据（0 命中）

```
$ rg -n 'isScsV39 \(restrictionCs' lean/Kepler/Text/*.lean
(无输出；LocalAuto30.lean:1201-1202 自述 "not present in any importable lane")

$ python3 -I check.py f_surr_localization_convex_local lemma_face_representation sum_face_rho_node1
? f_surr_localization_convex_local: 0 hits
? lemma_face_representation: 0 hits
? sum_face_rho_node1: 0 hits

$ rg -n 'theorem empty_' lean/Kepler/Text/*.lean
Kepler/Text/LocalAuto22.lean:2102:theorem empty_6T1_p22 (h : main_nonlinear_terminal_v11) ...
Kepler/Text/LocalAuto22.lean:2107:theorem empty_5T1_p22 (h : main_nonlinear_terminal_v11) ...
Kepler/Text/LocalAuto38.lean:3104:theorem empty_3T2 (h : main_nonlinear_terminal_v11) :
（OCBICBY 的 14 个目标系统中 12 个没有对应 empty_* 件）
```

TameLp 三条 LA7 前置：

```
+ WSEWPCH:      Text/LocalAuto7.lean:2214 sorry=True
+ FAN_PERIMETER:Text/LocalAuto7.lean:2207 sorry=True
+ BGMIFTE:      Text/LocalAuto7.lean:2142 sorry=True
```

---

## 7. 其余根节点（一段一条）

### LFLACKU_p23（LocalAuto23:303）

```
theorem LFLACKU_p23 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs3I1} ∅ := by
  sorry
/-- ... NEEDS: the `taustar_taum_dfun` / `FUNLIST_EXPLICIT` bridge (Terminal lane) to
reduce `MMsV39 scs3I1 = ∅` to `TAUM_STD_POS_p23`. -/

+ TAUM_STD_POS_p23:    LocalAuto23.lean:292 sorry=True
+ taustar_taum_dfun:   LocalAuto38.lean:1612 sorry=True
+ FUNLIST_EXPLICIT:    LocalAuto38.lean:1660 sorry=False
```

### VPWSHTO_p15（LocalAuto15:398）

```
theorem VPWSHTO_p15 : ∀ vv : ℕ → V3, ... ∃ i, i ∈ Set.Icc 0 4 ∧ ... := by
  sorry

+ VPWSHTO1_p15:   LocalAuto15.lean:303 sorry=True   (HOL 1698-1810 = 112 行)
+ VPWSHTO200_p15: LocalAuto15.lean:315 sorry=True   (HOL 1810-1864 = 54 行)
+ VPWSHTO2_p15:   LocalAuto15.lean:334 sorry=True   (HOL 1864-1919 = 55 行)
+ Section A 7 条: :222/:233/:242/:256/:267/:280/:293 全 sorry
```

LA15 文件头自述：「no external blocker existed; the other 12 remain the chapter's contract registry」——即真数学长链，不是缺件。

### URRPHBZ2（PackingAuto13:361）

```
theorem URRPHBZ2 (V : Set V3) (ul : List V3) (k : ℕ) (v : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hv : v ∈ V) :
    EventuallyRadial v (mcell k V ul) := by
  sorry

+ CLOSED_MCELL:                     PackingAuto12.lean:797  sorry=True
    （注释：k=0,1,3,4 已证，仅 k=2 缺 `IsClosed (affGe …)`）
+ U0_NOT_IN_CONVEX_HULL_FROM_ROGERS: PackingAuto12.lean:1060 sorry=True
    （注释：geometric giant）
```

### SCS_6I1_BERAK_BY_CSTAB（LocalAuto20:1647）

```
theorem SCS_6I1_BERAK_BY_CSTAB (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6I1} ({scs6T1} ∪ {x | ∃ i j, scsDiag 6 i j ∧ x = scsStabDiagV39 scs6I1 i j}) := by
  sorry
  -- DISCHARGES: hexagons.hl; arrow combining SCS_6I1_IMP_SCS_6T1 with the
  -- diag-stabilisation destinations.

+ SCS_6I1_IMP_SCS_6T1: LocalAuto20.lean:1638 sorry=True
+ SCS_6M1_IMP_SCS_6T1: LocalAuto20.lean:1627 sorry=True
    -- NEEDS: LocalAuto1 RRCWNSJ_concl (:3652) / JCYFMRP_concl (:3660) /
    --        JLXFDMJ_concl (:3699) / MXQTIED_concl (:3259)
+ PEDSLGV2:            LocalAuto20.lean:824  sorry=False  ← NEEDS 注记称 "proof pending"，已过时
```

### UAGHHBM_p30（LocalAuto30:1204）

```
theorem UAGHHBM_p30 (s : ScsV39) (i j : ℕ) (c : ℝ) (hs : isScsV39 s) ... :
    scsArrowV39 {s} {t | t ∈ subdivV39 s i j c} := by
  sorry
-- 注释（:1199-1202）: ... the remaining inputs are `isScsV39 (restrictionCs1V39 s i j c)` /
-- `isScsV39 (restrictionCs2V39 s i j c)`, not present in any importable lane.
-- 定义在 LocalAuto1.lean:915 / :921（def 本身无 sorry），但两条 isScs 引理全仓 0 命中。
```

### SCS_5M2_IMP_SCS_5T1_p29（LocalAuto29:3651）

```
theorem SCS_5M2_IMP_SCS_5T1_p29 : main_nonlinear_terminal_v11 →
    ∀ v : ℕ → V3, v ∈ MMsV39 scs5M2 → ... → MMsV39 scs5T1 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL terminal-nonlinear inequality machinery: the
  -- `scs_5M2` realisation with all diag distances `> cstab` realises
  -- `scs_5T1` with negative taustar.
（无具名前置；LA29 内 5T1 只有 SCS_5T1_IS_SCS_p29:771 / BASIC:1580 / K:1633 三条已证定义件）
```

### OCBICBY_p22（LocalAuto22:2674）

```
theorem OCBICBY_p22 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6T1} ∅ ∧ scsArrowV39 {scs5T1} ∅ ∧ ... (14 个合取) := by
  sorry
（依赖 empty_6T1_p22:2102 / empty_5T1_p22:2107 两条 giant；其余 12 系统无 empty_* 件）
```

### TameLp.fully_surrounded_perimeter_bound（TameLp.lean:925，namespace `Kepler.Text.TameLp`）

```
theorem fully_surrounded_perimeter_bound (V : Set V3) (E : Set (Set V3))
    (hfan : FAN 0 V E) (hsurr : FullySurrounded V E) :
    PerimeterBound V E hfan := by
  -- NEEDS（Lane G 侦察 2026-10-23）：卡具名桥——LocalAuto7（Polar_fan 移植）的
  -- 周长 lane `WSEWPCH`/`FAN_PERIMETER`/`BGMIFTE` 均为 faithful sorry 陈述
  -- ... 且 Local_lemmas 章的
  -- `f_surr_localization_convex_local`/`lemma_face_representation`/
  -- `sum_face_rho_node1` 未移植。
  sorry
```

### NUXCOEAv2_p28（LocalAuto28:8037，快照过时）

```
$ sed -n '8052,8055p' lean/Kepler/Text/LocalAuto28.lean
  exact NUXCOEA_p28 s k w l j ZLZTHIC_p14 MHAEYJN_p37 hk hk3 hs hmw haz hnc haff hj haj
    hbj hdiag1 hdiag2 hJ hlunar
（体非 sorry；探针 #print axioms = [propext, Classical.choice, Quot.sound]）
$ git log --oneline 7c59149c..HEAD -- lean/Kepler/Text/LocalAuto28.lean
ad7e9dba LA28 NUXCOEA 巨人双闭 (4->2): NUXCOEA_p28 (=2 半边, BBindex 真子集) + NUXCOEAv2_p28; 仅剩 2 条冻结 MIS-PORT
```

---

## 8. 仓内零改动

```
$ git -C /Users/zhangzhuo/repos/kepler-conjecture-lean4 status --porcelain
(空)
$ git -C /Users/zhangzhuo/repos/kepler-conjecture-lean4 rev-parse --short HEAD
b49461bb
```

所有草稿/脚本在 `/tmp/cone-text-triage-w1/`（`scan.py`、`analyze.py`、`roots.py`、`check.py`、`probe1.lean`、`probe1.log`）；产物在 `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/cone-text-triage-w1/`。

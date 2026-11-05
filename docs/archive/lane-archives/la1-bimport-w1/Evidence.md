# Evidence — lane la1-bimport-w1 (raw readings)

All commands: standalone `lean` with
`LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)`; logs captured with
`script -q` and read after `tr -d '\r'`.

## E1. Compile summaries

| log | `: error:` | `declaration uses `sorry`` | `warning:` lines |
|---|---|---|---|
| `base-la16.log` | 0 | 1 | 4 |
| `import-la16.log` | 0 | 1 | 4 |
| `base-la26.log` | 0 | 3 | 9 |
| `import-la26.log` | 0 | 3 | 9 |
| `ax-la16-base.log` | 0 | 1 | 4 |
| `ax-la16-mod.log` | 0 | 1 | 4 |
| `ax-la26-base.log` | 0 | 3 | 9 |
| `ax-la26-mod.log` | 0 | 3 | 9 |
| `bridge-probe-clean.log` | 0 | 0 | 0 |

## E2. Warning spectra (path/line stripped, file order)

### base-la16.log vs import-la16.log

```
base : ['`push_neg` has been deprecated. Prefer using `push Not` instead.', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'This simp argument is unused:', 'declaration uses `sorry`']
after: ['`push_neg` has been deprecated. Prefer using `push Not` instead.', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'This simp argument is unused:', 'declaration uses `sorry`']
identical: True
```

### base-la26.log vs import-la26.log

```
base : ['Try `simp at this` instead of `simpa using this`', 'declaration uses `sorry`', '`push_neg` has been deprecated. Prefer using `push Not` instead.', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'This simp argument is unused:', 'This simp argument is unused:', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'declaration uses `sorry`', 'declaration uses `sorry`']
after: ['Try `simp at this` instead of `simpa using this`', 'declaration uses `sorry`', '`push_neg` has been deprecated. Prefer using `push Not` instead.', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'This simp argument is unused:', 'This simp argument is unused:', '`push_neg` has been deprecated. Prefer using `push Not` instead.', 'declaration uses `sorry`', 'declaration uses `sorry`']
identical: True
```

## E3. Axiom probes — appended 12 (LA16) and 14 (LA26)

Baseline source is `git show HEAD:` at lane start; modified source is the
delivered file.  The appended prints appear once per probe; the LA16 file
also carries its own in-file `#print axioms` block (not part of the probe).

### LA16, baseline
```
'Kepler.Text.FSQKWKK_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_SHIFT_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.ear_acute_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_nonexist_849_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_diag_362_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.K_SUC_2_MOD_F_SUB_ID_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.real_continuous_taum_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_GENERIC_SYM_0_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.FSQKWKK_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_SHIFT_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.ear_acute_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_nonexist_849_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_diag_362_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.K_SUC_2_MOD_F_SUB_ID_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.real_continuous_taum_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_GENERIC_SYM_0_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BKOSSGE_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.JEJTVGB_p16' depends on axioms: [propext, sorryAx, choice, Quot.sound]
```
### LA16, after edge (same 12 + 6 donors)
```
'Kepler.Text.FSQKWKK_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_SHIFT_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.ear_acute_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_nonexist_849_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_diag_362_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.K_SUC_2_MOD_F_SUB_ID_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.real_continuous_taum_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_GENERIC_SYM_0_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.FSQKWKK_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XIVPHKS_SHIFT_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.ear_acute_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_nonexist_849_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.quad_diag_362_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.taum_dih_y_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.K_SUC_2_MOD_F_SUB_ID_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.real_continuous_taum_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_GENERIC_SYM_0_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BKOSSGE_p16' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.JEJTVGB_p16' depends on axioms: [propext, sorryAx, choice, Quot.sound]
'Kepler.Text.AUEAHEH_p33' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.VQFYMZY_p33' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BNAWVNH_p33' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.RAWZDIB_p33' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.MFKLVDK_p33' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.RYPDIXT_p33' depends on axioms: [propext, choice, Quot.sound]
```
### LA26, baseline
```
'Kepler.Text.PPBTYDQ_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.AXJRPNC_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BB_RHO_NODE_IVS_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.DIST_LE_2h0_IN_CASES_6_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.DIST_EDGE_IN_BB_LE_2_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.NORM_V_IN_BB_LE_CSTAB_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.MXQTIED_TAU_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_BASIC_DSV_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.J_EMPY_CASES_6_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BB_F_SUC_PRE_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.LUNAR_IN_V_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.WL_IN_E_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.RRCWNSJ_p26' depends on axioms: [propext, sorryAx, choice, Quot.sound]
```
### LA26, after edge (same 14 + 2 donors)
```
'Kepler.Text.PPBTYDQ_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.AXJRPNC_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BB_RHO_NODE_IVS_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.DIST_LE_2h0_IN_CASES_6_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.DIST_EDGE_IN_BB_LE_2_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.NORM_V_IN_BB_LE_CSTAB_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.MXQTIED_TAU_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.SCS_BASIC_DSV_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.J_EMPY_CASES_6_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.BB_F_SUC_PRE_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.LUNAR_IN_V_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.WL_IN_E_p26' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.RRCWNSJ_p26' depends on axioms: [propext, sorryAx, choice, Quot.sound]
'Kepler.Text.ODXLSTCv2_p28' depends on axioms: [propext, choice, Quot.sound]
'Kepler.Text.IMJXPHRv2_p28' depends on axioms: [propext, choice, Quot.sound]
```
### donor `#check` types (LA26 probe)
```
ODXLSTCv2_p28 : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
IMJXPHRv2_p28 : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
```
### donor `#check` types (LA16 probe)
```
AUEAHEH_p33 : scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1}
VQFYMZY_p33 : scsArrowV39 {scs4I3} {scs4M6', scs4T4}
BNAWVNH_p33 : scsArrowV39 {scs4M2} {scs4M6', scs3M1, scs3T4}
RAWZDIB_p33 : scsArrowV39 {scs4M3'} {scs4M6', scs3T1, scs3T6'}
MFKLVDK_p33 : scsArrowV39 {scs4M4'} {scs4M7, scs3T3, scs3M1, scs3T4}
RYPDIXT_p33 : scsArrowV39 {scs4M5'} {scs4M8, scs3T4}
```

## E4. Static import graph (post-edit working tree)
```
== post-edit static import graph audit (working tree = HEAD + lane edits) ==
cycle count:
0
LA16 closure size after edge:
113
LA26 closure size after edge:
110
edge LA16->LA33:
SAFE Kepler.Text.LocalAuto16 -> Kepler.Text.LocalAuto33 (no path Kepler.Text.LocalAuto33 ->* Kepler.Text.LocalAuto16)
edge LA26->LA28:
SAFE Kepler.Text.LocalAuto26 -> Kepler.Text.LocalAuto28 (no path Kepler.Text.LocalAuto28 ->* Kepler.Text.LocalAuto26)
reverse path LA33 ->* LA16:
NO PATH
reverse path LA28 ->* LA26:
NO PATH
proposed LA20->LA27:
CYCLE-IF-ADDED path Kepler.Text.LocalAuto27 ->* Kepler.Text.LocalAuto20:
Kepler.Text.LocalAuto27 -> Kepler.Text.LocalAuto24 -> Kepler.Text.LocalAuto20
proposed LA20->OdxlstcBridge:
CYCLE-IF-ADDED path Kepler.Text.OdxlstcBridge ->* Kepler.Text.LocalAuto20:
Kepler.Text.OdxlstcBridge -> Kepler.Text.LocalAuto31 -> Kepler.Text.LocalAuto18 -> Kepler.Text.LocalAuto27 -> Kepler.Text.LocalAuto24 -> Kepler.Text.LocalAuto20
```

## E5. K_MODULES evidence
```
== K_MODULES (docs/e2e-reachability-map.tsv header) ==
ROOT Kepler.Assembly.the_kepler_conjecture_from_interfaces
K_REACH 2085951
K_SORRIED 119
K_AXIOM 624
K_MODULES 4194
== each newly entered module already has reachable declarations in the map ==
LocalAuto33      0
LocalAuto29      0
LocalAuto28      0
LocalAuto18      0
LocalAuto31      0
LocalAuto34      0
OdxlstcBridge    0
== per-module map rows (module<TAB>decl) ==
582	Kepler.Text.LocalAuto33
466	Kepler.Text.LocalAuto34
435	Kepler.Text.LocalAuto28
432	Kepler.Text.LocalAuto29
224	Kepler.Text.LocalAuto18
161	Kepler.Text.LocalAuto31
5	Kepler.Text.OdxlstcBridge
LocalAuto33      1
LocalAuto29      1
LocalAuto28      1
LocalAuto18      1
LocalAuto31      1
LocalAuto34      1
OdxlstcBridge    1
```

## E6. LKGRQUI bridge probe (RC=0)
```
^D'Kepler.Text.LKGRQUI_p27' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LKGRQUI_krnl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.AQICLXA_SLICE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FUNOUYH_SLICE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LKGRQUI_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.AQICLXA' depends on axioms: [propext, Classical.choice, Quot.sound]
Kepler.Text.LKGRQUI_p27 : ∀ (s s' s'' : Kepler.Text.ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
  Kepler.Text.isScsV39 s →
    Kepler.Text.scsDiag s.k p q → Kepler.Text.isScsSliceV39 s s' s'' p q → Kepler.Text.scsArrowV39 {s} {s', s''}
Kepler.Text.LKGRQUI_krnl : ∀ (s s' s'' : Kepler.Text.ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
  Kepler.Text.isScsV39 s →
    Kepler.Text.scsDiag s.k p q → Kepler.Text.isScsSliceV39 s s' s'' p q → Kepler.Text.scsArrowV39 {s} {s', s''}
```

## E7. Baseline hashes and final hashes

`md5-baseline.txt` (lane start, current HEAD content for all files):
```
a224d3423e8cfcd56f8479c4f596ada2
78b3088caf43bbce68e07589acc901c7
cd3172826e8d1e0a9ab00563dfd1708b
b99ae8c58fbf11d625a0849eb2048e86
a630d4b5e3f5add808060e8b2c883b0b
f5fd80f33635d8fd295a081de846b4ae
```
Final delivered files (md5):
```
408e10083ad3b8baa2b13b45c7d8b843  LocalAuto16.lean (final = work copy)
da63f81041da1dca4e67d87ee7534de3  LocalAuto26.lean (final = work copy)
b99ae8c58fbf11d625a0849eb2048e86  OdxlstcBridge.lean (untouched)
cd3172826e8d1e0a9ab00563dfd1708b  LocalAuto20.lean (untouched)
a630d4b5e3f5add808060e8b2c883b0b  LocalAuto33.lean (donor module)
f5fd80f33635d8fd295a081de846b4ae  LocalAuto28.lean (donor module)
```

## E8. Diff gate
```
git apply --check --reverse kit-la1-bimport-w1.diff   -> OK (working tree exact)
git archive HEAD | tar -x -C <empty>; git apply --check kit-la1-bimport-w1.diff -> OK (clean HEAD)
```

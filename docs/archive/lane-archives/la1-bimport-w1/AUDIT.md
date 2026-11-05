# AUDIT — import edges (lane la1-bimport-w1)

Scope: the two import statements actually added, both against the working tree
`/Users/zhangzhuo/repos/kepler-conjecture-lean4` (lane start HEAD `8635c297`;
HEAD advanced to `873d2a2c` while the lane ran — the two target files are
byte-identical at both commits, md5 `a224d342…` / `78b3088c…`).  All probes are
standalone `lean` with `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)`;
no `lake`, no writes under `lean/.lake/`.

Logs: `logs/` (same names as below).  Compile logs are `script -q` captures,
stripped with `tr -d '\r'` before reading.

## 0. What was added

```
lean/Kepler/Text/LocalAuto16.lean   +1 import  Kepler.Text.LocalAuto33   (+4 comment lines)
lean/Kepler/Text/LocalAuto26.lean   +1 import  Kepler.Text.LocalAuto28   (+3 comment lines)
```

Diff: `kit-la1-bimport-w1.diff` (2 files, 9 inserted lines).

## 1. Audit A — static import graph acyclicity (both directions)

Tool: `importgraph.py` (source-level BFS over every `lean/**/*.lean`, `.lake`
excluded; 18,969-module scale same as recon).  Working tree = HEAD + lane edits.

```
cycle count (whole graph, Tarjan SCC):            0
edge LA16 -> LA33:  SAFE  (no path LA33 ->* LA16)
edge LA26 -> LA28:  SAFE  (no path LA28 ->* LA26)
reverse path LA33 ->* LA16:  NO PATH
reverse path LA28 ->* LA26:  NO PATH
```

Raw: `logs/graph-audit.txt`.

### Closure deltas (counting convention: transitive source imports, root and
### Mathlib-submodules not counted; `Mathlib` itself is one node)

| consumer | before | after | added modules |
|---|---|---|---|
| `LocalAuto16` | 111 | **113** | `LocalAuto33`, `LocalAuto29` |
| `LocalAuto26` | 105 | **110** | `LocalAuto28`, `LocalAuto18`, `LocalAuto31`, `LocalAuto34`, `OdxlstcBridge` |

The task predicted `+1` for LA16; the measured delta is **+2** because
`LocalAuto33` imports `LocalAuto29` (LA33:163) and LA16 does not import LA29.
This is a correction to RANKED §3's parenthetical (it said LA33's deps were
already all present).  LA26's delta is **+5**, as predicted.

## 2. Audit B — full-file warning spectrum, item-by-item

Normalisation: every `...: warning: <msg>` first line, in file order, path and
line number stripped.  Identical sequences = no warning drift; only line
numbers shift by the inserted comments (+5 LA16 / +4 LA26).

| file | baseline warnings | after | sequence |
|---|---|---|---|
| LocalAuto16 | 4 (2× `push_neg`, 1× unused simp arg `sub_dotProduct`, 1× sorry) | 4 | **IDENTICAL** |
| LocalAuto26 | 9 (1× unnecessarySimpa, 3× sorry, 3× `push_neg`, 2× unused simp arg `hab`) | 9 | **IDENTICAL** |

Raw logs: `logs/base-la16.log` vs `logs/import-la16.log`;
`logs/base-la26.log` vs `logs/import-la26.log`.

Both modified files: `RC=0`, `grep -c ': error:'` = **0**.

Own-sorry (`declaration uses sorry`):

| file | before | after |
|---|---|---|
| LocalAuto16 | 1 | **1** |
| LocalAuto26 | 3 | **3** |
| LocalAuto20 (untouched, md5 unchanged) | — | — |
| OdxlstcBridge (untouched, md5 unchanged) | — | — |

## 3. Audit C — `#print axioms` drift, ≥10 existing declarations per file

Probe method: pristine HEAD source + appended `#print axioms`, and modified
source + the same appended prints, both compiled standalone; the printed
`depends on axioms` lines are compared verbatim.

- `LocalAuto16`: 12 declarations —
  `FSQKWKK_p16`, `XIVPHKS_p16`, `XIVPHKS_SHIFT_p16`, `ear_acute_p16`,
  `quad_nonexist_849_p16`, `quad_diag_362_p16`, `taum_dih_y_p16`,
  `K_SUC_2_MOD_F_SUB_ID_p16`, `real_continuous_taum_p16`,
  `SCS_GENERIC_SYM_0_p16`, `BKOSSGE_p16`, `JEJTVGB_p16`.
  `diff` of the 12-line axiom output: **zero drift**.
- `LocalAuto26`: 14 declarations —
  `PPBTYDQ_p26`, `AXJRPNC_p26`, `BB_RHO_NODE_IVS_p26`,
  `DIST_LE_2h0_IN_CASES_6_p26`, `DIST_EDGE_IN_BB_LE_2_p26`,
  `NORM_V_IN_BB_LE_CSTAB_p26`, `XWNHLMD_MM_p26`, `MXQTIED_TAU_p26`,
  `SCS_BASIC_DSV_p26`, `J_EMPY_CASES_6_p26`, `BB_F_SUC_PRE_p26`,
  `LUNAR_IN_V_p26`, `WL_IN_E_p26`, `RRCWNSJ_p26`.
  `diff`: **zero drift** (13 std-3; `RRCWNSJ_p26` stays
  `[propext, sorryAx, choice, Quot.sound]`).

Note: `JEJTVGB_p16` remains `[propext, sorryAx, choice, Quot.sound]` after the
edge.  It is the only consumer of the six LA33 roots, but it also consumes
A-class `*_concl` arguments (`FYSSVEV_concl`, `ARDBZYE_concl`, `NWDGKXH_concl`,
`YOBIMPP_concl`, `MIQMCSN_concl`, `HIJQAHA_concl`, `OEHDBEN h`), so the edge
alone cannot flip its axiom face.  The six donors themselves are std-3
(below).  No LA16 closure is claimed.

Logs: `ax-la16-base.log` / `ax-la16-mod.log`, `ax-la26-base.log` /
`ax-la26-mod.log`.

## 4. Audit D — public-name collision grep

Method: extract every top-level `theorem/lemma/def/abbrev/structure/class/
inductive/instance` short name from the newly entered modules and intersect
with (a) the consumer file's own declarations, (b) every module that
transitively imports the consumer.

| edge | new modules | decl names | ∩ consumer | ∩ downstream |
|---|---|---|---|---|
| LA16→LA33 | LA33, LA29 | 333 + 201 | **0** | **0** (89 downstream modules) |
| LA26→LA28 | LA28, LA18, LA31, LA34, OdxlstcBridge | 178+111+105+258+7 | **0** | **0** (93 downstream modules) |

The compile itself is a second witness: a duplicate global name would make the
consumer fail with `already declared`, and both files are RC=0.

## 5. Audit E — `K_MODULES` increment

Definition (`docs/e2e-reachability-map.md:37`): K_MODULES = number of distinct
modules containing K_REACH declarations; global map baseline in
`docs/e2e-reachability-map.tsv` = **4,194**.

All seven newly entered modules already carry reachable declarations in the
map (one row each in the module histogram):

```
LocalAuto33 1   LocalAuto29 1   LocalAuto28 1   LocalAuto18 1
LocalAuto31 1   LocalAuto34 1   OdxlstcBridge 1
```

Therefore the global **K_MODULES does not move** (no module enters the cone
that was not already in it, matching RANKED §3).  What moves is only the
per-module import closure: **+2** / **+5** as tabulated in §1.  The task's
"expected +1/+5" is met for LA26 and corrected to +2 for LA16.

Raw: `logs/kmodules-audit.txt`.

## 6. Donor reachability and axiom face (pre-edge vs post-edge)

Probe `#check`/`#print axioms` appended to the modified consumer source
(the pre-edge state is the same probe against the pristine source, where the
donors are unknown identifiers — reproduced at HEAD by the recon's
`probe26.lean` and by LA26's missing names).

| donor | #check post-edge | #print axioms |
|---|---|---|
| `AUEAHEH_p33` | `scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1}` | std-3 |
| `VQFYMZY_p33` | `scsArrowV39 {scs4I3} {scs4M6', scs4T4}` | std-3 |
| `BNAWVNH_p33` | `scsArrowV39 {scs4M2} {scs4M6', scs3M1, scs3T4}` | std-3 |
| `RAWZDIB_p33` | `scsArrowV39 {scs4M3'} {scs4M6', scs3T1, scs3T6'}` | std-3 |
| `MFKLVDK_p33` | `scsArrowV39 {scs4M4'} {scs4M7, scs3T3, scs3M1, scs3T4}` | std-3 |
| `RYPDIXT_p33` | `scsArrowV39 {scs4M5'} {scs4M8, scs3T4}` | std-3 |
| `ODXLSTCv2_p28` | `∀ (s) (k) (w) (l), … → False` | std-3 |
| `IMJXPHRv2_p28` | `∀ (s) (k) (w) (l), … → a-equalities` | std-3 |

std-3 = `[propext, Classical.choice, Quot.sound]`.  `RRCWNSJ_p26` remains
`[propext, sorryAx, choice, Quot.sound]`.

## 7. Diff gate

```
git apply --check --reverse kit-la1-bimport-w1.diff   # working tree exact  -> OK
git archive HEAD | tar -x -C <empty dir>
git apply --check kit-la1-bimport-w1.diff             # clean HEAD tree     -> OK
```

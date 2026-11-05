# DELIVERY — lane `la1-bimport-w1` (LA1 registry B-class roots: wave→wave imports)

- Task: 9 B-class `*_concl` roots / 8 roots by safe import + 1 by bridge; main
  acceptance was `RRCWNSJ_p26` closure.
- Repo: `/Users/zhangzhuo/repos/kepler-conjecture-lean4`.
  Lane start HEAD `8635c297`; during the lane another lane advanced HEAD to
  `873d2a2c`.  The two target files are byte-identical at both commits
  (`git show 873d2a2c:… | md5` = `a224d342…` / `78b3088c…` = the lane's
  baseline md5), so every reading below is valid for the delivered tree.
- cwd `/tmp/la1-bimport-w1/`; artifacts `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/la1-bimport-w1/`.
- Discipline: no `lake`; no writes to `lean/.lake/`; standalone `lean` only
  with the prescribed `LEAN_PATH`; probes serial.

## 0. One-line result

**2 import statements landed (8 roots unlocked), bridge correctly declined,
`RRCWNSJ_p26` NOT closed (still `sorry`).**  Main repo changes are exactly the
two allowed source files (+9 lines total); `LocalAuto20` and
`OdxlstcBridge` untouched.  All five audits per edge pass; diff applies to a
clean HEAD.

| item | result |
|---|---|
| LA16 `import LocalAuto33` | landed; RC=0; 6 donors reachable, all std-3; own-sorry 1→1 |
| LA26 `import LocalAuto28` | landed; RC=0; `ODXLSTCv2_p28`/`IMJXPHRv2_p28` reachable, std-3; own-sorry 3→3 |
| LKGRQUI bridge | **declined**: requested shape is cyclic; no consumer remains; root already std-3 |
| `RRCWNSJ_p26` | **not closed**; blocking obligation isolated (`hnoLunar`) |
| LA16 six-root consumer | `JEJTVGB_p16` still `sorryAx` (A-class siblings in the same term) |
| `git apply --check` | forward on clean HEAD: OK; reverse on working tree: OK |

## 1. Edges (details in `AUDIT.md`)

```
lean/Kepler/Text/LocalAuto16.lean:  import Kepler.Text.LocalAuto33
lean/Kepler/Text/LocalAuto26.lean:  import Kepler.Text.LocalAuto28
```

Raw diffs: `kit-la1-bimport-w1.diff`.

Unlocked roots:

- LA16 / LA33: `AUEAHEH_concl`, `VQFYMZY_concl`, `BNAWVNH_concl`,
  `RAWZDIB_concl`, `MFKLVDK_concl`, `RYPDIXT_concl` — donors
  `*_p33`, all `#check`-reachable after the edge and all
  `[propext, Classical.choice, Quot.sound]`.
- LA26 / LA28: `ODXLSTCv2_concl`, `IMJXPHRv2_concl` — donors
  `ODXLSTCv2_p28`, `IMJXPHRv2_p28`, both reachable and std-3.  This removes
  the exact blocker recorded in `la26-rrcwnsj-w1/WORKORDER-next.md` §2 B1
  (route A).

Codegen/import evidence: line numbers shift by +5 (LA16) and +4 (LA26) only;
warning spectra identical item-by-item; 12 + 14 existing declarations show
zero axiom drift; zero name collisions with the consumer or any of the
89/93 downstream importers; global K_MODULES unchanged at 4,194 (all seven
newly entered modules were already in the map), per-module closure +2 / +5.

## 2. `LKGRQUI` — no bridge (see `BRIDGE.md`)

- `LocalAuto27 -> LocalAuto24 -> LocalAuto20` exists; so does
  `OdxlstcBridge -> LocalAuto31 -> LocalAuto18 -> LocalAuto27 -> LocalAuto24 -> LocalAuto20`.
  A module that LA20 imports **cannot** import LA27 without a cycle.
- `LKGRQUI_concl` has zero code references outside `LocalAuto1`; LA20's
  `AQICLXA_SLICE` / `FUNOUYH_SLICE` are already proved via
  `LkgrquiKernel.LKGRQUI_krnl` (std-3), and `LocalConcl.LKGRQUI_discharged`
  is std-3.
- Therefore: no change to `LocalAuto20.lean`, no change to
  `OdxlstcBridge.lean`, no new file.

## 3. `RRCWNSJ_p26` — not closed (honest status)

Target `LocalAuto26.lean:829` still has its original single `sorry`; own-sorry
stays 3.  `#print axioms RRCWNSJ_p26` remains
`[propext, sorryAx, choice, Quot.sound]`.

What is now true:

1. The previous lane's reduction
   `w5sgd_generic_of_no_lunar_p26 : isScsV39 s → MMsV39 s v → 3 < s.k →
   (¬∃ v' w, Lunar v' w (Set.range v) (Set.range fun i => {v i, v (i+1)})) →
   scsGeneric v` is machine-checked and std-3; it is carried in
   `Kit-draft-la26-rrcwnsj-w1.lean` (copied from `la26-rrcwnsj-w1/`, same md5).
2. The previous blocker is removed: `ODXLSTCv2_p28` / `IMJXPHRv2_p28` are now
   inside LA26's closure and std-3 (probe above).
3. The remaining obligation is exactly the HOL `RRCWNSJ.hl:274-861` case bash
   for `hnoLunar` (k = 6 distance-3 lunar pair).  Its two ingredients are:
   - the **ears disjunction** `‖v (x+1)‖ = 2 ∨ ‖v x - v (x+1)‖ = 2` (and the
     `x+k-1` mirror), which HOL derives from the minimiser structure of
     `MMs` (taustar/BBindex first-order conditions); and
   - the final `JKQEWGV3` (< π) vs `SYNQIWN` (> π) contradiction.
   The second ingredient is available and std-3.  The first is **not
   formalised anywhere in the tree**: a tree-wide grep for a lemma with a
   `2 < dist` / `2 < ‖·‖` conclusion finds nothing, and `MMsV39`
   (`LocalAuto1.lean:691`) only records the global `taustar`/`BBindex`
   minimality, not the vertex-move ear lemma.  Porting it is the 600-line HOL
   block, not 150–250 lines of glue; the previous lane reached the same
   conclusion after a full read of the HOL body.
   Inside this lane's 2-file allowance (`LocalAuto16/26`, `LocalAuto20`,
   `OdxlstcBridge`) the missing ear lemma cannot be imported from a lower
   module either: no such module exists (`grep` over all `Kepler/Text/*.lean`).

Delivery of the partial work:

- `Kit-draft-la26-rrcwnsj-w1.lean` — the verified reduction lemma, carried
  forward unchanged (not landed in `LocalAuto26.lean`, because it is not the
  target's proof and would be dead code at this HEAD).
- `WORKORDER-NEXT.md` is not rewritten; the previous lane's
  `la26-rrcwnsj-w1/WORKORDER-next.md` §3 remains the exact recipe, with its
  B1 blocker now discharged by this lane's import.

## 4. LA16 side — six roots unlocked, no new closure

The only consumer of the six `*_concl` roots is `JEJTVGB_p16`
(`LocalAuto16.lean:497-509`), which passes them to
`JEJTVGB_case_breakdown_p16` together with `FYSSVEV_concl`, `ARDBZYE_concl`,
`HIJQAHA_concl`, `NWDGKXH_concl`, `YOBIMPP_concl`, `MIQMCSN_concl`,
`OEHDBEN h`, …  All of those remain `sorryAx` (A-class, out of scope), so
`JEJTVGB_p16` remains `[propext, sorryAx, choice, Quot.sound]` and **no
declaration moves into the clean class**.  The six donors are now one rewrite
away (`AUEAHEH_p33` etc.), but the enclosing theorem still has non-B-class
inputs; closing it is an A-class lane, not this one.

## 5. Files

| path | content |
|---|---|
| `kit-la1-bimport-w1.diff` | 2-file diff (9 insertions), repo-relative headers |
| `final/LocalAuto16.lean`, `final/LocalAuto26.lean` | final file contents (md5-identical to the working tree and to `logs` compile inputs) |
| `Kit-draft-la26-rrcwnsj-w1.lean` | carried reduction lemma (std-3) |
| `AUDIT.md` | five audits per edge, raw readings |
| `BRIDGE.md` | bridge design / acyclicity proof / consumer audit |
| `Evidence.md` | raw `#print axioms` / `#check` / warning / graph output |
| `logs/` | all compile and probe logs |
| `md5-baseline.txt`, `importgraph.py` | baseline hashes, BFS tool |

## 6. Compile ledger

| file | command artifact | RC | errors | sorry warnings |
|---|---|---|---|---|
| `LocalAuto16.lean` baseline | `logs/base-la16.log` | 0 | 0 | 1 |
| `LocalAuto16.lean` + LA33 | `logs/import-la16.log`, `import-la16-w.log` | 0 | 0 | 1 |
| `LocalAuto26.lean` baseline | `logs/base-la26.log` | 0 | 0 | 3 |
| `LocalAuto26.lean` + LA28 | `logs/import-la26.log`, `import-la26-w.log` | 0 | 0 | 3 |
| LA16 axiom probe base/mod | `logs/ax-la16-{base,mod}.log` | 0/0 | 0/0 | — |
| LA26 axiom probe base/mod | `logs/ax-la26-{base,mod}.log` | 0/0 | 0/0 | — |
| LKGRQUI bridge probe | `logs/bridge-probe-clean.log` | 0 | 0 | — |

(`import-*-w.log` are a second launch from a different cwd; they fail at import
resolution because Lean treats cwd as an object-file root — kept only as a
tooling note, not as evidence.  The valid runs are `import-la16.log` /
`import-la26.log`.)

## 7. Budget

- Tool calls: ~57 / 120 at the time of writing; wall ~1.9 h / 3 h.
- Compiles: 10 standalone runs (2 base + 2 edge + 4 axiom probes + 1 bridge
  probe + 1 aborted-cwd rerun pair).
- No `lake`, no `lean/.lake/` writes, no other lane's scratch touched.

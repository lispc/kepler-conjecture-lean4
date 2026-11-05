# BRIDGE — the `LKGRQUI` case (lane la1-bimport-w1)

## 0. Result

**No bridge was created and `LocalAuto20` was not modified.**  The requested
shape ("bridge module imports `LocalAuto27`, then `LocalAuto20` imports the
bridge") is *provably cyclic*, and the premise that LA20 still consumes
`LKGRQUI_concl` is stale: LA20's two `LKGRQUI` instances were already
discharged in lane `m1a-root-w2` through `Kepler.Text.LkgrquiKernel`.  The
`LKGRQUI` root is already standard-three in the cone
(`LocalConcl.LKGRQUI_discharged`).  Nothing is owed here.

## 1. The requested bridge cannot be acyclic

Static source-import BFS (`importgraph.py`, whole `lean/` tree):

```
LA27 -> LA24 -> LA20                       (direct import edges)
OdxlstcBridge -> LA31 -> LA18 -> LA27 -> LA24 -> LA20
```

If a module `B` were imported by LA20 and imported LA27, the resulting graph
would contain `LA20 -> B -> LA27 -> LA24 -> LA20`, a cycle.  The same holds if
the existing `OdxlstcBridge.lean` (which imports only `LocalAuto31`) were made
to import LA27 and then imported by LA20: LA20 would gain
`LA20 -> OdxlstcBridge -> LA31 -> LA18 -> LA27 -> LA24 -> LA20`.

Measured:

```
python3 -I importgraph.py edge Kepler.Text.LocalAuto20 Kepler.Text.LocalAuto27
  CYCLE-IF-ADDED  Kepler.Text.LocalAuto27 -> Kepler.Text.LocalAuto24 -> Kepler.Text.LocalAuto20
python3 -I importgraph.py edge Kepler.Text.LocalAuto20 Kepler.Text.OdxlstcBridge
  CYCLE-IF-ADDED  OdxlstcBridge -> LA31 -> LA18 -> LA27 -> LA24 -> LA20
```

Raw: `logs/graph-audit.txt`.

A cycle is not a cosmetic problem: with Lake, building LA20 would need
`Bridge.olean`, which needs `LA27.olean`, which needs `LA20.olean`.  The lane
contract's own gate ("static import graph BFS acyclic, both directions") rules
the requested shape out.

## 2. `LKGRQUI_concl` has no wave consumer left

Tree-wide `grep -rn 'LKGRQUI_concl' --include='*.lean' lean/Kepler`:

| hit | nature |
|---|---|
| `LocalAuto1.lean:2880,2884` | the registry declaration itself (out of scope, immutable) |
| `LocalConcl.lean:2214` | docstring of the clean twin `LKGRQUI_discharged := LKGRQUI_p27` |
| `LocalAuto20.lean:28,31` | stale 2026-09-19 docstring ("all 7 blockers still open") |
| `LocalAuto27.lean:59`, `LocalAuto29.lean:76,160,3863` | docstrings/NEEDS comments |

No code reference exists.  LA20's actual `LKGRQUI` sites are:

```
LocalAuto20.lean:1345  theorem AQICLXA_SLICE ...
LocalAuto20.lean:1403  theorem FUNOUYH_SLICE ...
```

both discharged by `exact LKGRQUI_krnl …` (comments at :1350 and :1408 name
lane `m1a-root-w2`; `LkgrquiKernel` is imported at LA20:52).  The packaging
was deliberately re-proved *above* LA20 (the module imports LA35 +
`SgtrnafKernel` only) precisely because LA27 is above LA20.

## 3. Machine-checked axiom face (probe `logs/bridge-probe-clean.log`, RC=0)

```
'Kepler.Text.LKGRQUI_p27'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LKGRQUI_krnl'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.AQICLXA_SLICE'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FUNOUYH_SLICE'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LKGRQUI_discharged'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.AQICLXA'              depends on axioms: [propext, Classical.choice, Quot.sound]
```

with

```
LKGRQUI_p27 : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
  isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q → scsArrowV39 {s} {s', s''}
LKGRQUI_krnl : <the same type>
```

So the root is standard-three on both the wave donor (`_p27`) and the cone
twin (`_discharged`), and LA20's consumers are standard-three through the
kernel.  Importing LA27 into LA20's closure would add no axiom benefit.

## 4. What would be a legitimate bridge, if ever needed

A module below LA20 (importable by LA20 without a cycle) would have to contain
a *re-proof* of `LKGRQUI`, not a forward reference — exactly what
`Kepler.Text.LkgrquiKernel` already is (`LkgrquiKernel.lean:43`,
`LKGRQUI_krnl`, std-3; closure 87 modules, no LA27).  The existing
`OdxlstcBridge.lean` is the precedent for the *other* pattern (re-mirroring an
upper module's `Prop` bodies so the consumer never imports the upper module);
that pattern is inapplicable here because `LKGRQUI` is a theorem, not a
`Prop`-shaped data definition, and its proof is already available below LA20.

## 5. Conclusion

- `OdxlstcBridge.lean`: untouched (md5 `b99ae8c5…`).
- `LocalAuto20.lean`: untouched (md5 `cd317282…`).
- No new bridge file: a file with the requested import would either be
  unimportable by LA20 (cycle) or dead code.

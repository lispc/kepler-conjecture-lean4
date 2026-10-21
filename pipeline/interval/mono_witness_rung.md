# W8 mono-tree witness-rung policy (BIXPCGW_7274157868_a sb12-heavy)

Stable recipe (gen-8): `--mono-tree --mono-witness-rung=64`.

This flag is **off by default**. With no rung flag the emitter output is
byte-identical to the pre-W8 emitter (gen-3..7 discipline, re-verified in
gen-8 on the t3 stage-A/stage-B artifacts).

## What the policy does

`--mono-witness-rung=64` lowers the Taylor rung **only at the trans nodes
whose values feed a DomOK v2 witness row** (divisor / guard / radicand
subtrees). On BIXPCGW sb12-heavy that is **8 of 53** trans nodes; the other
**45** tight-margin trans nodes keep the spec rung (2048, -64). The DomOK
discharge consumes only the *sign* of a witness value, and `transOn_sound`
holds at every rung; the TM leaf certificate consumes tight margins, so its
nodes stay at the spec rung.

## Rung curve (gen-7, POS1 and L1 boxes agree row-for-row)

The 99 DOM witness rows (74 `div` + 25 `rad`, `domEvals` order) were graded
at uniform rungs 8/16/32/64/128/256:

| rung | admissible rows | non-admissible rows | stage-A wall (POS1/L1) | leaf probe |
|------|-----------------|---------------------|------------------------|------------|
| 8    | 97/99           | rows 3, 52 (`div`)  | 6.5~15.3 s*            | FAIL       |
| 16   | 97/99           | rows 3, 52          | 6.7~7.1 s              | FAIL       |
| 32   | 97/99           | rows 3, 52          | 6.4~6.5 s              | FAIL       |
| 64   | **99/99**       | —                   | 9.9 s                  | NEG (uniform) |
| 128  | 99/99           | —                   | 12.7~15.3 s            | NEG        |
| 256  | 99/99           | —                   | 31.7~31.8 s            | NEG        |

\* first run includes Lean olean cold start (51.1 s).

Per-row minimum admissible rung (`gen7/POS1.minrung.json`,
`gen7/L1.minrung.json`; identical series, `nonmonotone_rows=[]`):

```
row:  0         1         2         3         4         5         6
      8884888888888888888888888888888888888888888888888888488888888888
      8888888888888888888888888888888888888888888888888888888888888888
      8888888888888888888888888888888888888888888888888888888888888888
```

Only rows 3 and 52 (both `div`) need 64; no row needs >64. Machine-readable
copy: `pipeline/interval/mono_witness_rung.json`.

## Witness line vs final-value line (the structural fact)

Lowering witness rows is cheap and sound, but it does **not** certify the
leaf final value: `checkPosTMHull` on a leaf still needs the constant bits
at 2048. The keepconst policy (`--mono-dom-rung-keepconst=256/2048`) is
what keeps a leaf probe PASS. Gen-7 pricing: uniform-64 DOM bake 9.9 s vs
keepconst-256 bake 612 s (62x), while the leaf hull decide is ~250 s per
leaf. The tree policy therefore is:

- internal node DOM discharge: rung <= 64 (`--mono-witness-rung=64`);
- leaf hull: keep the constant-bit policy (`keepconst-2048`).

The gen-7 t2/t3 split-tree pilots (no restrict nodes) and the gen-8 kd
producer both carry these markers. Whether the single mixed `wr64`
expression is enough for a leaf hull is exactly what
`gen7/POS1_wr64.*` / the gen-8 rerun measures; if the probe is PASS, one
`wr64` expression serves both lines.

## Provenance

- Curve: `gen7/{POS1,L1}.rungcurve.json`, `gen7/*_u{8..256}.stageA_run.log`,
  min-rung JSONs, `gen7/REPORT.md` section 1.
- Constant in the emitter: `W8_WITNESS_RUNG_SB12HEAVY = 64`
  (`pipeline/interval/emit_lean.py`).
- Emitter flag: `--mono-witness-rung=N[,OUT]` (`OUT` defaults to the spec
  `rung_out`).

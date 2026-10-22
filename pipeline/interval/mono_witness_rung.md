# W8 mono-tree witness-rung policy (BIXPCGW_7274157868_a sb12-heavy)

Stable recipe (gen-9 correction): `--mono-tree --mono-dom-rung-keepconst=128`
(128 and 256 are cost-equivalent; 128 is the minimal provable rung).
The gen-8 `--mono-witness-rung=64` recipe is **not** the tree policy: its
unified expression is the cost anomaly (>3342 s, no DOM rows). See the
gen-9 closure below.

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

The gen-9 measurement closed this question: a single **unified
keepconst-128** expression passes both the 99/99 DOM rows and the leaf hull
probe, so no split-expression Lean bridge is needed. The mixed `wr64`
expression is not cheaper — it is the anomaly (no DOM rows after 3342 s).
The leaf-hull rung threshold is in (64, 128]: keepconst-64 NEG,
keepconst-128 PASS. kd split trees have zero restrict nodes, so the
split-expression saving (~165 s per restrict node) does not apply to the
251k-leaf tree.

## gen-9 closure (2026-10-21, same-wave measurements)

All numbers below are same-machine, serial, load average ~1.9-2.3 (no
cross-wave load inflation).

- **Leaf hull rung threshold ∈ (64, 128]**: keepconst-64 NEG (231.6 s);
  keepconst-128 PASS (241.7 s). Uniform-64 is NEG even on a narrow kd d2
  leaf; the constant bits at 2048 are necessary.
- **kc128 ≈ kc256**: stage-A 426.2 s vs 411.2 s; stage-B decide 178.9 s vs
  188.4 s; DOM tables identical (0/99 row difference). gen-5's 612.3 s for
  kc256 was load 9-11 inflation (≈1.49×), not recipe cost.
- **Unified expression works**: keepconst-128 stage-A yields DOM 99/99
  admissible **and** leaf probe PASS; stage-B kernel decide rc=0, 0 error.
  Split expressions would save ~165 s per restrict node but need a
  cross-expression DOM bridge — not worth it for kd split trees.
- **Real t3 end-to-end @kc128**: stage-A 604.3 s (3/3 PASS) + kernel decide
  209.4 s = **813.7 s**, rc=0, 0 error, peak RSS 23.4 GB. gen-8's 1119.1 s
  included cross-wave load; normalized it agrees. No 1.37× speedup claim.
- **kd integration**: case root d3 = 8/8 guard-straddle (0 green, 8/8 probe
  FAIL after emit); POS1 root d2/d3 all POS (4/4, 8/8 green). Per-leaf
  kc128 e2e: POS1 d2 4/4 green (209-215 s + 145-151 s); d3 sample green
  (198.6 s + 146.5 s). Depth histogram: first screen-pass depth POS1 = 0
  (the root itself suffices; deeper kd is wasted), case ≤3 none; coverage
  POS1 100%, case 0%. Face-literal audit: 18 specs, zero errors.
- **Cost model**: per leaf ≈210 s bake + ≈150 s decide ≈ 360 CPU-s; the bake
  is dominated by the 8 box-independent constant trans@2048. 251k leaves
  ≈ 9.0e7 CPU-s ≈ 1046 CPU-days serial. Memory, not CPU, caps concurrency:
  stage-A ≈5.6 GB (×5-6 per 36 GB node), decide peak 17.2-24.2 GB
  (×1 per 36 GB, ×2 per 64 GB).
- **gen-10 direction**: no emitter change needed (md5 unchanged; gen-5
  replay byte-identical). Highest leverage = bake the constant-trans boxes
  into `TMParams` on the Lean side (potential 40-80 CPU-s/leaf, 251k
  ≈116-232 CPU-days) plus kd "stop at first screen-pass" policy.
- Provenance: `gen9/REPORT.md`, `gen9/COMMANDS.md`, `gen9/manifest.md5`
  (160 files), under `lane_snapshots/w8rung/`.

## gen-10 probe (2026-10-22, clone-only; no main-repo code change)

Question: bake the 8 box-independent constant trans boxes into `TMParams`?
Answer: the `TMParams` route is **NO-GO**, but a library constant box for
`atan(1)` is **GO**.

- The 8 constants are 6× `atan(1)` (π/4) and 2× `atan(1/√2)` (≈0.61548).
  Cost is concentrated in the two `atanq` at N=2048 (~99.9 s each); each
  `atan1` is ~2.2 s. Uniform-128 without a constant box is NEG because
  `atan(1)`'s rung-128 interval (~0.0039) is too coarse.
- Prototype (clone only): `pi4D` constant box in
  `lean/Kepler/Interval/Trans.lean` (`pi4D_mem` kernel-checked from Mathlib
  `pi_gt_d20`/`pi_lt_d20`, no new axioms); `arctanI` returns it on `[1,1]`;
  `atanq` drops to rung 128 (residual ~1e-41). Emitter default path is
  byte-identical.
- POS1 unified: stage-A 426.2→**9.51 s**, decide 178.9→**42.71 s**
  (total 605.1→**52.22 s**, 11.6×); DOM 99/99, leaf probe PASS; decide RSS
  17.18→**8.90 GB**.
- t3 three leaves: 813.7→**92.73 s** (8.8×), 3/3 PASS, kernel rc=0, no new
  axioms; RSS 23.42→12.48 GB.
- Per leaf ≈**50 CPU-s** (vs 360); 251k leaves ≈**145 CPU-days** (vs 1046);
  64 cores ≈2.3 days; a 36 GB node fits 3 decide workers (vs 1), so memory
  is no longer the hard one-worker-per-node constraint.
- `TMParams` full bake: **NO-GO** — no value-box field, the soundness chain
  needs 400-600 lines / 3-5 rounds, and the incremental benefit here is zero.
- Adoption options: (a) global `arctanI` fast path — changes the `atan(1)`
  interval semantics for all old artifacts, old params/DOM tables must be
  regenerated; (b) opt-in `TKind.atan1K` — preserves default semantics,
  +1-2 rounds. **Pending user decision; nothing has landed in the main repo.**
- Provenance: `gen10/REPORT.md`, `gen10/code.diff`, snapshot
  `lane_snapshots/w8rung/gen10probe/` (65 items, manifest.md5).

## Provenance

- Curve: `gen7/{POS1,L1}.rungcurve.json`, `gen7/*_u{8..256}.stageA_run.log`,
  min-rung JSONs, `gen7/REPORT.md` section 1.
- Constant in the emitter: `W8_WITNESS_RUNG_SB12HEAVY = 64`
  (`pipeline/interval/emit_lean.py`).
- Emitter flag: `--mono-witness-rung=N[,OUT]` (`OUT` defaults to the spec
  `rung_out`).

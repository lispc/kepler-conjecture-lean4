# `wt1emit` — the 221 generated `W1DC_*.lean` modules

`lean/Kepler/Text/TaylorSecond/W1DC_*.lean` (221 files, 777,090 lines,
65,404,398 B) are **generated artifacts, not tracked source**.  They are
reproduced byte-for-byte from the four untrusted generators and one data file
in this directory.

## One command

```sh
python3 -I lean/scripts/wt1emit/gen_all.py     # or: make gen-wt1
```

That is a **no-op** when the files on disk already match `manifest.sha256`
(mtimes are preserved, so no rebuild is triggered); it creates or repairs
whatever is missing or stale.  A clean checkout therefore only needs this one
command before compiling:

```sh
make gen-wt1
cd lean && lake env lean Kepler/Text/TaylorSecond/W1DCAssemblyFinal.lean   # island protocol
```

`make check-wt1` (hash only, no generation, no Lean) is the guard used by CI
and by hand; `lean/scripts/check_wt1_generated.py` is the same check as a
standalone script.

Requirements: Python ≥ 3.11 (`sys.set_int_max_str_digits`), no Lean, no network,
no external paths — everything the generators need is in this directory.

## Tracked source vs. generated artifact

| tracked (in git) | generated (git-ignored) |
|---|---|
| `boxes221.json` — the 221 box records (base, case, path, mode, nleaves, ylo/yhi, T2) | `../../Kepler/Text/TaylorSecond/W1DC_*.lean` — 221 modules |
| `gen_m9.py`, `dcrep.py`, `node_table.py` — value-function emitter | |
| `mk_l1.py` — L1 rewriting pass (drop per-node `ev_/p_/op_` lemmas, restate 4 root facts as whole-tree `rfl`) | |
| `gen_all.py` — driver, `manifest.sha256` — expected sha256 of all 221 | |

The rest of `TaylorSecond/` is ordinary tracked source: the 13 kit modules,
`W1aFJet.lean`, the 10 `W1DCAssembly*.lean` modules and the other hand-written
files.  Only the `W1DC_*.lean` glob is generated (`W1DC15873.lean`,
`W1DCBridge.lean`, `W1DCTermPilot.lean`, `W1DCAssembly*.lean` are tracked).

## Trust

The generators are **untrusted**: they only propose literals and proof terms.
Every emitted `rfl`/`decide` obligation is re-checked by the Lean kernel when
the module is compiled, and each of the 221 modules prints 8 `#print axioms`
results (all ⊆ `{propext, Classical.choice, Quot.sound}`; `val_facts` is
`[propext, Quot.sound]`).  No `axiom` / `sorry` / `admit` / `native_decide` is
ever emitted.  Regenerating changes nothing in the trust base: same bytes →
same oleans → same root face (`#print axioms
Kepler.the_kepler_conjecture_e2e` = 585 `native_decide` + the standard three +
`sorryAx`).

## Provenance

* `manifest.sha256` — 221 `<sha256>  <repo-relative path>` lines, computed from
  the **committed blobs of `7855a963`** (not from generator output).
* generator sha256 (must match the snapshots they came from):
  * `gen_m9.py` `05e5f9bdd066261a2506dcea512be7d15a1cc787b91e8be3ee0d2cb6ca77f8f4`
  * `dcrep.py`  `48cdd7eb0ae059b4fab4f131b52aa07905380204e4eca8baccd9cdbf2a9d6fe1`
  * `node_table.py` `a4e2027c33595c56f232ccdfcffbe885df425771751a3122aba0fcf0e6bc3170`
  * `mk_l1.py`  `ba30fc7a5122406b3ce5ad1ff95f8da5ed55faabaf272fe8f56799ce3a92f43e`
  * `boxes221.json` `ea721aada74f1614bb7b814976fbbeb13040ec30a92ac005617947a4f9d6a8e5`
* the only edit to the snapshots is `gen_m9.py`'s `BOXES_DEFAULT`, which now
  points at `os.path.join(HERE, 'boxes221.json')` instead of a
  `~/c17_backup/...` path.  Nothing else differs; the emitted bytes are
  identical (verified 221/221 against `7855a963`).

## Driver options

```
--out-dir DIR        target directory (default lean/Kepler/Text/TaylorSecond)
--only <stem>        one box id, repeatable
--check              emit into a temp dir, compare, write nothing
--verify-manifest    hash the files on disk against manifest.sha256 (no generation)
--if-missing         accepted for readability; skipping up-to-date files is the default
--force              rewrite even when the hash already matches
```

`gen_all.py` refuses to install a file whose sha256 differs from
`manifest.sha256` (`DRIFT <box>`), so generator drift can never silently reach
the tree: fix the generator (and re-record the manifest only through a reviewed
commit), never the expectation.

## Determinism / regression check

```sh
python3 -I lean/scripts/wt1emit/gen_all.py --force --out-dir /tmp/a
python3 -I lean/scripts/wt1emit/gen_all.py --force --out-dir /tmp/b
diff -r /tmp/a /tmp/b            # empty; also 221/221 identical to 7855a963
```

Runtime: ~16 s for all 221 boxes (single process, pure Python).
Recompiling all 221 modules is **not** part of this check and is not expected
(13,445.6 s CPU, see `docs/priority-queue.md`); compiled oleans stay valid as
long as the bytes match.

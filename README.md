# The Kepler Conjecture, Re-Proven in Lean 4

[中文版 README](README.zh.md)

An end-to-end formal proof of the **Kepler conjecture** in **Lean 4 + Mathlib**,
rebuilt with a certificate-based computation paradigm:

> The supremum of the density of congruent sphere packings in Euclidean 3-space
> is **π / √18 ≈ 0.74048**.

This is not a re-invention of the proof. The blueprint is Hales'
*Dense Sphere Packings* (Cambridge, 2012) — the book that was written to be
formalized — with the Flyspeck project (HOL Light/Isabelle, 2014) as a
read-only reference, not an input. Every computational claim (graph
enumeration, linear programs, nonlinear inequalities) is backed by a
**certificate checked by a small verified checker**; no generator or solver
code is ever trusted.

## Design principles

- **Certifying algorithms.** Untrusted generators (plantri/nauty, SoPlex /
  QSopt_ex, dReal, Arb/FLINT) produce certificates; Lean-side checkers verify
  them inside the kernel. The trusted base is the Lean kernel plus small
  checkers — nothing else.
- **`native_decide` is banned project-wide** (it would pull the compiler into
  the trusted base), with one chartered, scoped exception: the Phase 2 graph
  enumeration shards (**585 shard axioms as of 2026-11-09** — declared trust
  base, frozen; footprint in `DECISIONS.md` / `docs/trust-base.md`).
- **Statement fidelity is the single quality valve.** The final statement is
  semantically aligned with Flyspeck's `the_kepler_conjecture`; all deviations
  are registered in `docs/statement-fidelity.md`, and statement changes only
  land through the SF channel (`docs/statement-fix-proposals.md`).
- **Honest accounting.** Sorries carry `-- NEEDS` annotations; the live
  operational ledger (`docs/priority-queue.md`) and the live axiom face of the
  end-to-end theorem are the objective progress meters. Unverifiable evidence
  is downgraded, not kept. Numbers are either measured (with a commit and date)
  or marked stale — never hand-copied between documents.

## Repository layout

```
kepler-conjecture-lean4/
├── README.md / README.zh.md
├── PLAN.md                 # 2026-10-10 plan snapshot (not current status)
├── DECISIONS.md            # decision log (the only current root-level doc)
├── lean/                   # the Lean 4 project (toolchain v4.32.2, elan-pinned)
│   ├── Kepler/Statement.lean     # Phase 1: the theorem statement
│   ├── Kepler/Final.lean         # Phase 6: end-to-end theorem `the_kepler_conjecture_e2e`
│   ├── Kepler/Assembly.lean      # Phase 6: assembly spine (four interfaces)
│   ├── Kepler/Graphs/            # Phase 2: tame graph enumeration checkers
│   ├── Kepler/LP/                # Phase 3: LP certificate checkers
│   ├── Kepler/Interval/          # Phase 4: interval/Taylor certificate checkers
│   ├── Kepler/Geom/              # volume/measure/azimuth foundations
│   ├── Kepler/Text/              # Phase 5: text-proof porting modules
│   └── scripts/                  # gates, debt ledger, generators
├── pipeline/               # untrusted generators/solver wrappers (never trusted)
├── certificates/           # certificate registry (SHA-256 + reproduction commands)
├── reference/              # read-only clones (flyspeck et al., LOCK.md pins hashes)
└── docs/
    ├── README.md           # navigation: what to read for what
    ├── priority-queue.md   # the live ledger: in-flight + queue + recent log
    ├── archive/            # history (scouts / handoffs / projects / lane-archives /
    │                       #   root docs). Read-only testimony, not current state.
    ├── assets/             # artifacts/drafts/probe logs
    └── statement-fix-proposals-patches/  # SF-channel patch archive (active)
```

## Building and verifying

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain,
currently **Lean v4.32.2**, is pinned by `lean/lean-toolchain`).

```sh
make build     # cd lean && lake build
make check     # build + axiom audit (no sorryAx, no self-introduced axioms
               # beyond the chartered shard exceptions)
make reprove   # clean rebuild from scratch + audit — the Definition of Done
```

Note: heavy recomputation (LP re-run, nonlinear certificate replays) is
currently deferred pending a strong machine; see the compute-constraint table
in `PLAN.md` §5. Pure Lean compilation work runs on the baseline laptop.

## Status (as of 2026-11-09)

The end-to-end object `Kepler.the_kepler_conjecture_e2e` stands. Its live axiom
face is **589 lines** = **585 `native_decide` graph shard axioms** (the declared
trust base, frozen 2026-11-09: 580 shard-range + 5 tri-single-seed, two shapes
only) + `propext` + `Classical.choice` + `Quot.sound` + `sorryAx` (55 cone
sorries — the only real debt; baseline AM `98414950`, 2026-11-14).

**Terminal standard (user ruling 2026-11-06, `AGENTS.md` §1)**: no worse than
Flyspeck/Isabelle — i.e. the 585 declared shard axioms (same class and same
data as Isabelle's `by eval`) + a zero-`sorryAx` goal. **Not** "standard three
alone" — "true standard-three" is explicitly out of scope (the 23 goodList
facts are already kernel-proved, matching HOL).

Phase-level status (qualitative — **live numbers live in one place only**):

| Phase | Content | Status |
|---|---|---|
| 1 | Theorem statement | ✅ statement fixed |
| 2 | Tame plane graph enumeration | ✅ 19,715 graphs + completeness proved; 585 shard axioms = declared trust base (data three-way reconciled SAME with the original) |
| 3 | Linear programming | ✅ 43,078 terminal LP certificates checked; LP checkers kernel-proved; fill debt = `lpArchiveCertificatesDebt` (in cone) |
| 4 | Nonlinear inequalities | 🟡 hNL six-component: 5 interface sorries (`nli*`); sqrt/atan-tier heavy farm replay deferred (the original used a farm too) |
| 5 | Text proof porting | 🟡 geometry towers largely collapsed (LA engine layer: 16 files at zero sorries); §5 two roots under attack (J campaign `jcajydu` + WSEWPCH program) |
| 6 | Integration & delivery | 🟡 e2e stands, assembly chain proved; root face 589; trust-base manifest `--check` green |

**Where to read the numbers.** There is exactly one live ledger:
[`docs/priority-queue.md`](docs/priority-queue.md) — in-flight lanes, queue,
recent landings, and the tower dashboard. Metric definitions and the cone /
union reachability baselines are in
[`docs/e2e-reachability-map.md`](docs/e2e-reachability-map.md). Older
dashboards (`STATUS.md`, `HANDOFF.md`, `DEBT.md`) are archived under
[`docs/archive/root/`](docs/archive/root/) as read-only testimony frozen at
2026-10-23. Decisions are in
[`DECISIONS.md`](DECISIONS.md); the phase plan (a 2026-10-10 snapshot, not
current status) is in [`PLAN.md`](PLAN.md).

The live debt graph of the main theorem is still one command:

```lean
#print axioms Kepler.the_kepler_conjecture_e2e
```

## References

- T. Hales, *Dense Sphere Packings: A Blueprint for Formal Proofs*, Cambridge, 2012
- T. Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum of Mathematics, Pi, 2017
- T. Hales, *Some algorithms arising in the proof of the Kepler conjecture*, arXiv:math/0205209
- Flyspeck: `flyspeck/flyspeck`, `flyspeck/kepler98`; mathlib4: `leanprover-community/mathlib4`
- Tools: plantri/nauty, SoPlex, QSopt_ex, VIPR, dReal, Arb/FLINT

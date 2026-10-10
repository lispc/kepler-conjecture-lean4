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
  enumeration shards (624 shard axioms, footprint recorded in `DECISIONS.md`).
- **Statement fidelity is the single quality valve.** The final statement is
  semantically aligned with Flyspeck's `the_kepler_conjecture`; all deviations
  are registered in `docs/statement-fidelity.md`, and statement changes only
  land through the SF channel (`docs/statement-fix-proposals.md`).
- **Honest accounting.** Sorries carry `-- NEEDS` annotations; the debt ledger
  (`DEBT.md`) and the live axiom face of the end-to-end theorem are the
  objective progress meters. Unverifiable evidence is downgraded, not kept.

## Repository layout

```
kepler-conjecture-lean4/
├── README.md / README.zh.md
├── PLAN.md                 # authoritative plan + current strategy (Chinese)
├── STATUS.md               # live progress dashboard (refreshed per batch)
├── DEBT.md                 # sorry debt ledger (generated)
├── DECISIONS.md            # decision log
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
└── docs/                   # living references at root level;
    ├── scouts/             #   recon reports (filed once written)
    ├── handoffs/           #   lane handoffs & session logs
    ├── projects/           #   per-lane designs & roadmaps
    ├── assets/             #   artifacts/drafts/probe logs
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

## Current status (2026-10-10)

| Phase | Content | Status |
|---|---|---|
| 1 | Theorem statement | ✅ done (placeholder sorry to retire at final assembly) |
| 2 | Tame plane graph enumeration | ✅ 19,715 graphs + completeness certificates, kernel-verified |
| 3 | Linear programming | ✅ 43,078 terminal LPs kernel-verified (re-run artifacts pending, see PLAN §5) |
| 4 | Nonlinear inequalities | 🟡 solver layer 68/176 trusted-closed, 8 cases kernel-closed; heavy compute deferred |
| 5 | Text proof porting | 🟡 hypermap/fan/topology/planarity/Conforming/polyhedron complete; packing+local skeletons 100%, proof filling in rolling batches |
| 6 | Integration & delivery | 🟡 end-to-end object `the_kepler_conjecture_e2e` stands; 3 frozen interface sorries + final dedup remain |

The authoritative, continuously updated sources of truth are `STATUS.md`
(dashboard), `DEBT.md` (debt ledger), `PLAN.md` (plan + strategy), and
`DECISIONS.md` (decision log). The live debt graph of the main theorem is:

```lean
#print axioms Kepler.the_kepler_conjecture_e2e
```

## References

- T. Hales, *Dense Sphere Packings: A Blueprint for Formal Proofs*, Cambridge, 2012
- T. Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum of Mathematics, Pi, 2017
- T. Hales, *Some algorithms arising in the proof of the Kepler conjecture*, arXiv:math/0205209
- Flyspeck: `flyspeck/flyspeck`, `flyspeck/kepler98`; mathlib4: `leanprover-community/mathlib4`
- Tools: plantri/nauty, SoPlex, QSopt_ex, VIPR, dReal, Arb/FLINT

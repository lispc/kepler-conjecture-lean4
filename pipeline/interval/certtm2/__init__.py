"""certtm2 — CertTM2/d2B production leaf-certificate emitter (Python side).

This package is the productionised form of the `g4port-w1` prototype
(`scripts/{jet2,tmcore,engine_lipsch,pilot_run,dump_leaves,leaf_valid}.py`):

  * `jetlib`   : backend-generic second-order forward AD (Jet = value,
                 gradient, Hessian).  Port of the prototype `jet2.py`,
                 including both documented fixes (interval squaring via the
                 tight square; corner-safe `sqrt` coefficient hook).
  * `nav`      : float navigation backend (fast, ~1e-15, NOT a certificate).
  * `dyad`     : certified dyadic-interval backend built on the bit-exact
                 `tmexact.py` replica of the Lean interval kernel
                 (Dyadic/DInterval ops, sqrtI/sqrtRel, arctanI, halfPiI).
                 Every scalar is an outward-rounded dyadic interval, so a
                 box evaluation is a machine-checkable enclosure.
  * `exprs`    : backend-generic pilot expression builders
                 (dihY/solY/lmfun-side/gamma4/main/margin; port of the
                 prototype `tmcore.py` with the sound deltaX corner lift).
  * `engine`   : deterministic best-first B&B (L1 T2 node, L2 local mono
                 FIX, L3 concavity glue, L4 adaptive split; port of
                 `engine_lipsch.py`).
  * `emit_tm2` : CLI.  Runs the B&B in float-nav mode (reproducing the
                 g4port s-curve leaf counts), then re-certifies every
                 closed leaf with the C1 supplier (symbolic second
                 derivatives evaluated as dyadic-interval enclosures over
                 the box: fC/gC thin, GB/HB full-box) and emits one
                 schema'd JSON certificate per leaf
                 (`schema: certtm2-leaf-cert/1.0`, see SCHEMA.md).
  * `audit`    : per-leaf sampling audit (float, prototype口径, and
                 mpmath 60-dps high precision) + g4port TSV comparator.

Determinism contract: identical inputs give byte-identical JSON output.
All certificate data is exact (dyadic integer pairs / exact rationals);
floats appear only as navigation values and are emitted with `repr`
(shortest round-trip).  No wall-clock values are written to JSON.

Trust discipline (AGENTS §2): this emitter never touches Lean; it produces
DATA.  Soundness of a certificate ultimately rests on the future Lean
`CertTM2.lean` checker replaying these fields, not on the emitter.
"""

VERSION = "1.0"
SCHEMA = "certtm2-leaf-cert/1.0"

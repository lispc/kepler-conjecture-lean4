/-
Phase 2 acceptance gate G2: the tame plane graph classification theorem.

Assembles `RelativeCompleteness.completeness` with the four per-seed
certificate facts `same_0`–`same_3` (Tri: hand-written pilot in
`CertTri.lean`; Quad/Pent/Hex: generated wiring in `CertQuad/Pent/Hex.lean`
over the shard files in `CertShards/`).

The computational content (worklist closure + final iso checks) is evaluated
by `native_decide` under the scoped exception recorded in DECISIONS.md
(2026-08-10); all assembly proofs are pure kernel proofs.
-/
import Kepler.Graphs.CertTri
import Kepler.Graphs.CertQuad
import Kepler.Graphs.CertPent
import Kepler.Graphs.CertHex

namespace Kepler.Graphs

/-- **G2**: every tame plane graph is isomorphic (in the sense of
`PlaneGraphIso.iso_fgraph`, which allows mirror images) to a graph in the
Flyspeck-Tame Archive. -/
theorem tame_classification {g : Graph} (hpg : PlaneGraphs g) (ht : tame g) :
    inIso g.fgraph Archive :=
  completeness same_0 same_1 same_2 same_3 hpg ht

end Kepler.Graphs

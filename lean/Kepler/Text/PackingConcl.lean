/-
Kepler.Text.PackingConcl — ASSEMBLY file: discharges the `pack_concl.hl`
interface statements of `Kepler.Text.PackingAuto2` (and the `OXLZLEZ1.hl`
family of `PackingAuto3`) from their downstream proved twins.

WHY AN ASSEMBLY FILE
  Every sorried `*_concl` in PackingAuto2 names a downstream twin that is
  supposed to discharge it, but the twins live in files that IMPORT
  PackingAuto2 (PackingAuto5/6/7/9/10/11/12/13/16/17/19/22/23/24/25), so
  Auto2 cannot cite them without an import cycle.  This file imports the
  full chain and performs the discharges.

LEDGER (honest accounting; ground truth = `#print axioms`, not prose)
  Sorried `*_concl` interfaces found .................... 62
    PackingAuto2 (pack_concl.hl family) .................. 52
      (the 53rd, `RHWVGNP_concl`, is term-proved in place from
      `VORONOI_POLYHEDRON_concl`, hence still sorryAx-tainted upstream)
    PackingAuto3 (OXLZLEZ1.hl family) ..................... 9
    PackingAuto24 (`GRUTOTI1_concl_p24`) .................. 1
  DISCHARGED here (sorry-free, `#print axioms` verified) ..  3
    EMNWUUS1_concl        <- PackingAuto9.EMNWUUS1
    VORONOI_BALL2_concl   <- PackingAuto5.VORONOI_BALL2  (hypothesis-shim)
    DRUQUFE_concl         <- PackingAuto5.DRUQUFE
  BLOCKED ............................................... 59, reasons:

  (a) Twin does not exist (no downstream proved statement at all): 2
      RVFXZBU1_concl, RVFXZBU2_concl (Auto2:743,750; no RVFXZBU1/RVFXZBU2
      twin anywhere in Auto3-25).

  (b) Twin is itself `sorry`-ed: 30
      Auto7: XYOFCGX, XNHPWAB1..4, WAUFCHE1/2, YIFVQDV, KSOQKWL, IVFICRK,
        WQPRRDY (the whole Rogers part B cluster);
      Auto5: TIWWFYQ, VORONOI_INTER_BIS_LE, VORONOI_POLYHEDRON;
      Auto6: KHEJKCI;  Auto10: RVFXZBU (= RVFXZBU3 twin), HDTFNFZ;
      Auto13: URRPHBZ2, SLTSTLO1, SLTSTLO2;
      Auto16: QZYZMJC, KIZHLTL1/2/3;  Auto19: RDWKARC;  Auto22: GOTCJAH;
      Auto23/24: GRUTOTI1_concl / GRUTOTI1_concl_p24 (both sorried; the
        Auto23 olean is absent from this checkout anyway);
      Auto24: REUHADY, REUHADY_concl_version2 (REUHADY_p24 /
        REUHADY_version2_p24 sorried; Auto24 olean absent);
      Auto3 family: all 9 (CHQSQEY/MTMLSRF/LXDEYBO/UNPNFVW/IPVICGW/
        RSIWAMP/UTEOITF/LUIKGMH/GRHIDFA_concl) — their Auto4 twins are
        sorried too.

  (c) Twin looks proved but is sorryAx-tainted (verified by
      `#print axioms`): 15
      Auto6: GLTVHUM, DUUNHOR, QXSKIIT, OAPVION1/2/3 — their "proofs" are
        literally `exact <the sorried Auto2 concl>` (circular re-exports);
      Auto6: MHFTTZN1/2/4 (via sorried `MHFTTZN_lemma(2)`);
      Auto9: EMNWUUS2 (cites the circular `OAPVION2`);
      Auto10: URRPHBZ1 (via sorried `MEASURABLE_MCELL`);
      Auto11: LEPJBDJ, LEPJBDJ_0 (case lemmas sorryAx-tainted);
      Auto17: URRPHBZ3 (via `hdtfnfz_p17` -> LEPJBDJ chain);
      Auto12: MXI_EXISTS (its `MXI_EXPLICIT` cites the sorried concl);
      Auto19: UPFZBZM (via sorried `NEGLIGIBLE_FUNC`/`FCC_COMPATABILITY_FUNC`);
      Auto25: OXLZLEZ (additionally needs the two bank antecedents
        `pack_nonlinear_non_ox3q1h`/`ox3q1hP25` that `OXLZLEZ_concl`
        does not carry — a verbatim discharge is impossible even modulo
        the sorryAx taint).

IMPORT SET
  This file imports the maximal clash-free chain
  PackingAuto 2,3,5,6,7,8,9,10,11,12,13,16,17,19,21,25 (all oleans built).
  Excluded, deliberately:
    PackingAuto1  — Space3-based `saturated`/`Packing` CLASH by full name
                    with the Auto2 encodings; no module can import both.
    PackingAuto18/20 — mutually clashing `Kepler.Text.atn2`; neither hosts
                    a twin.
    PackingAuto22 — hosts only the (sorried) GOTCJAH twin; kept out to
                    hold the closure clash-free.
    PackingAuto23/24 — oleans absent from this checkout.

SHIMS
  VORONOI_BALL2_concl: the Auto2 interface carries `Packing V → v ∈ V →`
  before `saturated V`; PackingAuto5.VORONOI_BALL2 needs ONLY
  `saturated V` (the cell-subset-ball fact is saturation alone), so the
  two extra hypotheses are discharged by discarding them.  The other two
  discharges are shape-verbatim.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto9
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto16
import Kepler.Text.PackingAuto17
import Kepler.Text.PackingAuto19
import Kepler.Text.PackingAuto21
import Kepler.Text.PackingAuto25

namespace Kepler.Text

open Kepler.Geom Set Classical EuclideanGeometry

/-! ## Discharges (PackingAuto2 `pack_concl.hl` interfaces) -/

/-- `PackingAuto2.EMNWUUS1_concl` (Auto2:716), discharged by
`PackingAuto9.EMNWUUS1` (EMNWUUS.hl:56).  Shape-verbatim. -/
theorem EMNWUUS1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → (hl ul < Real.sqrt 2 ↔ mcell4 V ul ≠ ∅) :=
  EMNWUUS1

/-- `PackingAuto2.VORONOI_BALL2_concl` (Auto2:885), discharged by
`PackingAuto5.VORONOI_BALL2` (pack3.hl:767).  Shim: the twin needs only
`saturated V`; the interface's `Packing V` and `v ∈ V` are discarded. -/
theorem VORONOI_BALL2_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V → v ∈ V →
      voronoiClosed V v ⊆ Metric.ball v 2 :=
  fun V v _ hs _ => VORONOI_BALL2 V v hs

/-- `PackingAuto2.DRUQUFE_concl` (Auto2:909), discharged by
`PackingAuto5.DRUQUFE` (pack3.hl:970).  Shape-verbatim. -/
theorem DRUQUFE_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      IsCompact (voronoiClosed V v) ∧ Convex ℝ (voronoiClosed V v) ∧
        MeasurableSet (voronoiClosed V v) :=
  DRUQUFE

-- Self-check: each `_discharged` theorem must be free of `sorryAx`.
-- The compile log should list only `[propext, Classical.choice, Quot.sound]`
-- for all three.
#print axioms EMNWUUS1_concl_discharged
#print axioms VORONOI_BALL2_concl_discharged
#print axioms DRUQUFE_concl_discharged

end Kepler.Text

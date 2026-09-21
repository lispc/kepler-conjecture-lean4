/-
Kepler.Text.PackingConcl — ASSEMBLY file: discharges the `pack_concl.hl`
interface statements of `Kepler.Text.PackingAuto2` (and the `OXLZLEZ1.hl`
family of `PackingAuto3`) from their downstream twins.

WHY AN ASSEMBLY FILE
  Every sorried `*_concl` in PackingAuto2 names a downstream twin that is
  supposed to discharge it, but the twins live in files that IMPORT
  PackingAuto2 (PackingAuto4-25), so Auto2 cannot cite them without an
  import cycle.  This file imports the full chain and performs the
  discharges.

MODE (2026-09-21, end-to-end assembly turn)
  The spine is truthy: `Kepler/Assembly.lean`'s `textCapstone` consumes
  `PackingAuto25.PACKING_CHAPTER_MAIN_CONCLUSION`.  An entry here therefore
  no longer mirrors the upstream `sorry`; it APPLIES the downstream twin
  (`exact twin ...`) even when that twin's own proof is still sorryAx-
  tainted — the axiom flows along the proof term, so this file's debt
  graph is the real reachable-debt expansion of the chapter.  An entry
  keeps `sorry` only when NO twin exists or the twin's shape genuinely
  mismatches (the mismatch is documented at the entry).

LEDGER (honest accounting; ground truth = `#print axioms`, not prose)
  Sorried `*_concl` interfaces found .................... 62
    PackingAuto2 (pack_concl.hl family) .................. 52
      (the 53rd, `RHWVGNP_concl`, is term-proved in place from
      `VORONOI_POLYHEDRON_concl`)
    PackingAuto3 (OXLZLEZ1.hl family) ..................... 9
    PackingAuto24 (`GRUTOTI1_concl_p24`) .................. 1
      (private statement-copy of Auto2's `GRUTOTI1_concl`;
      accounted by the GRUTOTI1 entry below — 61 explicit
      entries + this 1 accounted copy = 62)
  WIRED here (`exact twin ...`, sorryAx flows through where the twin or
  a bank antecedent is sorried) ........................ 43
    verbatim twin (term-level `:= twin` / eta) ........... 38
    shim/bridge ........................................... 5
      VORONOI_BALL2  <- PackingAuto5.VORONOI_BALL2 (discard unused
        `Packing V` / `v ∈ V`)
      MHFTTZN4       <- PackingAuto6.MHFTTZN4 (rewrite `q` to the
        circumcenter)
      KHEJKCI        <- PackingAuto6.KHEJKCI (`vorList` → `.1 barV`)
      KIZHLTL1       <- PackingAuto16.KIZHLTL1 (its public
        `voronoiOpenP16` is delta-equal to Auto2's PRIVATE
        `voronoiOpen`; statement here carries the unfolded body)
      OXLZLEZ        <- PackingAuto25.OXLZLEZ (the twin's two bank
        antecedents `pack_nonlinear_non_ox3q1h`/`ox3q1hP25` are
        upstream `Prop := sorry` placeholders — supplied `by sorry`
        here, so the twin's REAL by_contra kernel
        (CELL_CLUSTER_ESTIMATE_PROPS + GRHIDFA_concl) is on the
        reachable path)
  BLOCKED ............................................... 19, reasons:

  (a) Twin does not exist: 2
      RVFXZBU1_concl, RVFXZBU2_concl (Auto2:743,750; no twin anywhere
      in Auto3-25).

  (b) Twin exists but is NOT statement-compatible (shape mismatch,
      documented at the entry): 7
      DUUNHOR (twin carries extra `Packing V`/`saturated V` the
        interface does not);
      XYOFCGX (twin needs `Packing V`, interface has none);
      IVFICRK (twin's second conjunct has two extra antecedents
        `i ∈ Icc 0 (k+1)`, `permutes σ (Icc 0 k)`);
      RVFXZBU3 (twin PA10.RVFXZBU is restricted to `i ∈ {0,1,2,3,4}`,
        interface quantifies over all `i`);
      MXI_EXISTS (PA12.MXI_EXPLICIT consumes this very interface —
        self-loop — and needs `ul = [u0,u1,u2,u3]` plus
        `hl (truncateSimplex 2 ul) < sqrt 2`, none carried);
      GOTCJAH (PA22.GOTCJAH is a different encoding: `fchanged c = WF`
        vs `topologicalComponentYfan`, `asn` vs `Real.arcsin`,
        `0 ∈ interior P` + facet-cardinality vs the interface's
        nonempty-facet/component hypotheses; PA22 not imported);
      GRUTOTI1 (only twin is PRIVATE `PackingAuto24.GRUTOTI1_concl_p24`
        — unreachable from any other module).

  (c) Twin exists only in a parallel PRIVATE encoding: 9 (the whole
      Auto3 OXLZLEZ1.hl family) — CHQSQEY, MTMLSRF, LXDEYBO, UNPNFVW,
      IPVICGW, RSIWAMP, UTEOITF, LUIKGMH, GRHIDFA_concl: the Auto4
      twins live over a `private structure CC4P4` with private accessors
      (ccBoolModelP4, ...), a parallel encoding of Auto3's `CcV11`
      interfaces; neither statement nor constants are referable here.

IMPORT SET
  PackingAuto 2,3,4-skipped,5,6,7,8,9,10,11,12,13,16,17,19,21,24,25 plus
  the transitive closure 14,15,18,20 (via 17/19/21/25 — the PA25 cc-block
  delegation and PA21/PA25 bring PA18/PA20 in anyway; neither hosts a
  twin).  Deliberately NOT imported:
    PackingAuto1  — Space3-based `saturated`/`Packing` CLASH by full name
                    with the Auto2 encodings; no module can import both.
    PackingAuto4  — its 9 OXLZLEZ2 twins are private-CC4P4-encoded and
                    therefore unusable; no other twin lives there.
    PackingAuto22 — hosts only the shape-mismatched GOTCJAH twin; kept
                    out to hold the closure clash-free.
    PackingAuto23 — hosts no twin.
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
import Kepler.Text.PackingAuto24
import Kepler.Text.PackingAuto25

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory EuclideanGeometry

/-! ## Discharges (PackingAuto2 `pack_concl.hl` interfaces) -/

/-- `PackingAuto2.GLTVHUM_concl` (Auto2:548), discharged by
`PackingAuto6.GLTVHUM` (Rogers.hl:1152).  Shape-verbatim. -/
theorem GLTVHUM_concl_discharged :
    ∀ (V : Set V3) (u0 p : V3), Packing V ∧ saturated V → u0 ∈ V →
    (p ∈ voronoiClosed V u0 ↔
      ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0]) :=
  fun V u0 p h hu0 => GLTVHUM V u0 p h hu0

/-- `PackingAuto2.DUUNHOR_concl` (Auto2:555).  TWIN MISMATCH:
`PackingAuto6.DUUNHOR` (Rogers.hl:1682) carries `Packing V` and
`saturated V` antecedents that the interface does not carry (its own
docstring calls them unused) — the twin is inapplicable to a bare
`barV`-only `V`. -/
theorem DUUNHOR_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3), barV V 3 ul → barV V 3 vl →
      rogers V ul ≠ rogers V vl → Coplanar (rogers V ul ∩ rogers V vl) := by
  sorry

/-- `PackingAuto2.QXSKIIT_concl` (Auto2:561), discharged by
`PackingAuto6.QXSKIIT` (Rogers.hl:3732).  Shape-verbatim. -/
theorem QXSKIIT_concl_discharged :
    ∀ {A : Type} (vf : A → V3) (b : A → ℝ),
    (vf '' (Set.univ : Set A)).Finite → ¬affineDependent (vf '' (Set.univ : Set A)) →
    (∀ i j : A, vf i = vf j → b i = b j) →
    ∃! p : V3, p ∈ (affineSpan ℝ (vf '' (Set.univ : Set A)) : Set V3) ∧
      ∀ i j : A, p ⬝ᵥ (vf i - vf j) = b i - b j :=
  @QXSKIIT

/-- `PackingAuto2.OAPVION1_concl` (Auto2:570), discharged by
`PackingAuto6.OAPVION1` (Rogers.hl:3843).  Shape-verbatim. -/
theorem OAPVION1_concl_discharged :
    ∀ S : Set V3, S ≠ ∅ → ¬affineDependent S →
      circumcenter S ∈ (affineSpan ℝ S : Set V3) :=
  OAPVION1

/-- `PackingAuto2.OAPVION2_concl` (Auto2:576), discharged by
`PackingAuto6.OAPVION2` (Rogers.hl:3851).  Shape-verbatim. -/
theorem OAPVION2_concl_discharged :
    ∀ S : Set V3, ¬affineDependent S →
      ∀ w ∈ S, radV S = dist (circumcenter S) w :=
  OAPVION2

/-- `PackingAuto2.OAPVION3_concl` (Auto2:582), discharged by
`PackingAuto6.OAPVION3` (Rogers.hl:3892).  Shape-verbatim. -/
theorem OAPVION3_concl_discharged :
    ∀ S : Set V3, ¬affineDependent S →
      ∀ p : V3, p ∈ (affineSpan ℝ S : Set V3) → (∃ c : ℝ, ∀ w ∈ S, dist p w = c) →
        p = circumcenter S :=
  OAPVION3

/-- `PackingAuto2.MHFTTZN1_concl` (Auto2:589), discharged by
`PackingAuto6.MHFTTZN1` (Rogers.hl:4862) — the twin needs neither
`k ≤ 3` nor saturation, so the interface's weaker hypotheses suffice. -/
theorem MHFTTZN1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul → affDim (setOfList ul) = (k : ℤ) :=
  fun V ul k _ _ hP hbar => MHFTTZN1 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN2_concl` (Auto2:595), discharged by
`PackingAuto6.MHFTTZN2` (Rogers.hl:4871).  The interface's `bis` is a
PRIVATE def of PackingAuto2, so the statement here carries its unfolded
body; `exact` closes the goal by delta on that def. -/
theorem MHFTTZN2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul →
      ∀ p : V3, p ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) ↔
        ∀ u ∈ setOfList ul, p ∈ {x : V3 | dist x (hdV ul) = dist x u} :=
  fun V ul k _ _ hP hbar => MHFTTZN2 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN3_concl` (Auto2:604), discharged by
`PackingAuto6.MHFTTZN3` (Rogers.hl:4881).  Shape-verbatim. -/
theorem MHFTTZN3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), k ≤ 3 → saturated V →
      Packing V → barV V k ul →
      ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩
          (affineSpan ℝ (setOfList ul) : Set V3)) =
        {circumcenter (setOfList ul)} :=
  fun V ul k _ _ hP hbar => MHFTTZN3 V ul k hP hbar

/-- `PackingAuto2.MHFTTZN4_concl` (Auto2:612), discharged by
`PackingAuto6.MHFTTZN4` (Rogers.hl:4985) — shim: the twin states the
orthogonality at the circumcenter; the interface's `q` is rewritten to
it by its defining hypothesis. -/
theorem MHFTTZN4_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (u v q : V3), k ≤ 3 →
      saturated V → Packing V → barV V k ul → q = circumcenter (setOfList ul) →
      u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) →
      v ∈ (affineSpan ℝ (setOfList ul) : Set V3) →
      (u - q) ⬝ᵥ (v - q) = 0 :=
  fun V ul k u v q _ _ hP hbar hq hu hv => by
    rw [hq]; exact MHFTTZN4 V ul k u v hP hbar hu hv

/-- `PackingAuto2.XYOFCGX_concl` (Auto2:621).  TWIN MISMATCH:
`PackingAuto7.XYOFCGX` (Rogers.hl:6559) requires `Packing V`, which the
interface does not carry (nor do the `XYOFCGX_*_0` case lemmas). -/
theorem XYOFCGX_concl_discharged :
    ∀ (V S : Set V3) (p : V3), S ⊆ V → ¬affineDependent S →
      p = circumcenter S → radV S < Real.sqrt 2 →
      ∀ u v : V3, u ∈ S → v ∈ V \ S → dist v p > dist u p := by
  sorry

/-- `PackingAuto2.XNHPWAB1_concl` (Auto2:629), discharged by
`PackingAuto7.XNHPWAB1` (Rogers.hl:7194) — the twin needs neither `k ≤ 3`
nor saturation. -/
theorem XNHPWAB1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      omegaList V ul = circumcenter (setOfList ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB1 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB2_concl` (Auto2:636), discharged by
`PackingAuto7.XNHPWAB2` (Rogers.hl:7497). -/
theorem XNHPWAB2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      omegaList V ul ∈ convexHull ℝ (setOfList ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB2 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB3_concl` (Auto2:642), discharged by
`PackingAuto7.XNHPWAB3` (Rogers.hl:7926). -/
theorem XNHPWAB3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      affDim {omegaListN V ul j | j ∈ Finset.Icc 0 k} = (k : ℤ) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB3 V ul k hP hbar hl2

/-- `PackingAuto2.XNHPWAB4_concl` (Auto2:648), discharged by
`PackingAuto7.XNHPWAB4` (Rogers.hl:7691). -/
theorem XNHPWAB4_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → k ≤ 3 → barV V k ul → hl ul < Real.sqrt 2 →
      ∀ i j : ℕ, i < j → j ≤ k →
        hl (truncateSimplex i ul) < hl (truncateSimplex j ul) :=
  fun V ul k _ hP _ hbar hl2 => XNHPWAB4 V ul k hP hbar hl2

/-- `PackingAuto2.WAUFCHE1_concl` (Auto2:656), discharged by
`PackingAuto7.WAUFCHE1` (Rogers.hl:8186). -/
theorem WAUFCHE1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul ≤ dist (omegaList V ul) (hdV ul) :=
  fun V ul k _ hP hbar => WAUFCHE1 V ul k hP hbar

/-- `PackingAuto2.WAUFCHE2_concl` (Auto2:661), discharged by
`PackingAuto7.WAUFCHE2` (Rogers.hl:8249). -/
theorem WAUFCHE2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      hl ul = dist (omegaList V ul) (hdV ul) :=
  fun V ul k _ hP hbar hl2 => WAUFCHE2 V ul k hP hbar hl2

/-- `PackingAuto2.YIFVQDV_concl` (Auto2:667), discharged by
`PackingAuto7.YIFVQDV` (Rogers.hl:9118) — hypothesis reorder only. -/
theorem YIFVQDV_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ),
      Packing V → saturated V → barV V k ul → hl ul < Real.sqrt 2 →
      permutes p (Set.Icc 0 k) →
      barV V k (leftActionList p ul) ∧
        omegaList V (leftActionList p ul) = omegaList V ul :=
  fun V ul k p hP _ hbar hl2 hperm => YIFVQDV V ul k p hP hbar hl2 hperm

/-- `PackingAuto2.KSOQKWL_concl` (Auto2:676), discharged by
`PackingAuto7.KSOQKWL` (Rogers.hl:9588) — hypothesis reorder only. -/
theorem KSOQKWL_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ),
      saturated V → Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      permutes p (Set.Icc 0 k) →
      rogers V ul = rogers V (leftActionList p ul) → p = Equiv.refl ℕ :=
  fun V ul p k _ hP hbar hl2 hperm hrog =>
    KSOQKWL V ul p k hP hbar hl2 hperm hrog

/-- `PackingAuto2.IVFICRK_concl` (Auto2:684).  TWIN MISMATCH:
`PackingAuto7.IVFICRK` (Rogers.hl:9929) carries the same BijOn witness
but its second conjunct has two EXTRA antecedents (`i ∈ Icc 0 (k+1)`,
`permutes σ (Icc 0 k)`) that the interface's pointwise statement does
not allow — the twin is strictly weaker than the interface. -/
theorem IVFICRK_concl_discharged :
    ∀ {A : Type} [Inhabited A] (k : ℕ),
      ∃ g : ℕ × Equiv.Perm ℕ → Equiv.Perm ℕ,
        Set.BijOn g {q : ℕ × Equiv.Perm ℕ | q.1 ∈ Set.Icc 0 (k + 1) ∧
            permutes q.2 (Set.Icc 0 k)}
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k + 1))} ∧
        ∀ (ul : List A) (i : ℕ) (σ : Equiv.Perm ℕ) (j : ℕ), ul.length = k + 2 →
          j ≤ k →
          (leftActionList (g (i, σ)) ul).getD j default =
            (leftActionList σ (dropIth ul i)).getD j default := by
  sorry

/-- `PackingAuto2.WQPRRDY_concl` (Auto2:699), discharged by
`PackingAuto7.WQPRRDY` (Rogers.hl:10534). -/
theorem WQPRRDY_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V k ul → hl ul < Real.sqrt 2 →
      convexHull ℝ (setOfList ul) =
        ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 k)}) :=
  fun V ul k _ hP hbar hl2 => WQPRRDY V ul k hP hbar hl2

/-- `PackingAuto2.MXI_EXISTS_concl` (Auto2:708).  NO USABLE TWIN: the
only downstream carrier, `PackingAuto12.MXI_EXPLICIT` (marchal2.hl:2516),
consumes THIS interface in its own proof (self-loop) and additionally
needs `ul = [u0,u1,u2,u3]` and `hl (truncateSimplex 2 ul) < sqrt 2`,
neither derivable from the interface's hypotheses (barV does not bound
proper truncations). -/
theorem MXI_EXISTS_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → Real.sqrt 2 ≤ hl ul →
      mxi V ul ∈ convexHull ℝ {omegaListN V ul 2, omegaListN V ul 3} ∧
        dist (mxi V ul) (hdV ul) = Real.sqrt 2 := by
  sorry

/-- `PackingAuto2.EMNWUUS1_concl` (Auto2:716), discharged by
`PackingAuto9.EMNWUUS1` (EMNWUUS.hl:56).  Shape-verbatim. -/
theorem EMNWUUS1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → (hl ul < Real.sqrt 2 ↔ mcell4 V ul ≠ ∅) :=
  EMNWUUS1

/-- `PackingAuto2.EMNWUUS2_concl` (Auto2:721), discharged by
`PackingAuto9.EMNWUUS2` (EMNWUUS.hl:81).  Shape-verbatim. -/
theorem EMNWUUS2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul →
      (hl ul < Real.sqrt 2 ↔
        mcell0 V ul = ∅ ∧ mcell1 V ul = ∅ ∧ mcell2 V ul = ∅ ∧ mcell3 V ul = ∅) :=
  fun V ul hs hp hbar => EMNWUUS2 V ul hs hp hbar

/-- `PackingAuto2.SLTSTLO1_concl` (Auto2:727), discharged by
`PackingAuto13.SLTSTLO1` (SLTSTLO.hl).  Shape-verbatim. -/
theorem SLTSTLO1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (p : V3), saturated V →
      Packing V → barV V 3 ul → p ∈ rogers V ul →
      ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul :=
  fun V ul p hs hp hb hpr => SLTSTLO1 V ul p hs hp hb hpr

/-- `PackingAuto2.SLTSTLO2_concl` (Auto2:734), discharged by
`PackingAuto13.SLTSTLO2` (SLTSTLO.hl:582).  Shape-verbatim. -/
theorem SLTSTLO2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3),
      ∃ Z : Set V3, ∀ p : V3, saturated V → Packing V → barV V 3 ul →
        nullSet Z ∧ (p ∈ rogers V ul \ Z → ∃! i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul) :=
  SLTSTLO2

/-- `PackingAuto2.RVFXZBU1_concl` (Auto2:741).  NO TWIN: no downstream
module states the cross-list null-overlap fact (PA13's SLTSTLO2 proof
notes it as NEEDS RVFXZBU1/Auto10, which never landed). -/
theorem RVFXZBU1_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3) (i j : ℕ), saturated V →
      Packing V → barV V 3 ul → barV V 3 vl → i ≠ j →
      nullSet (mcell i V ul ∩ mcell j V vl) := by
  sorry

/-- `PackingAuto2.RVFXZBU2_concl` (Auto2:748).  NO TWIN anywhere in
Auto3-25 (permutation-forcing from non-null same-index overlap). -/
theorem RVFXZBU2_concl_discharged :
    ∀ (V : Set V3) (ul vl : List V3) (i : ℕ), saturated V →
      Packing V → barV V 3 ul → barV V 3 vl →
      ¬nullSet (mcell i V ul ∩ mcell i V vl) →
      ∃ p : Equiv.Perm ℕ, permutes p (Set.Icc 0 (i - 1)) ∧ vl = leftActionList p ul := by
  sorry

/-- `PackingAuto2.RVFXZBU3_concl` (Auto2:756).  TWIN MISMATCH:
`PackingAuto10.RVFXZBU` (its ENCODING-FIX twin) is restricted to
`i ∈ {0,1,2,3,4}` (its `i = 2,3` branches are still sorried), while the
interface quantifies over ALL `i`; for `i ≥ 5` the tail-fixedness window
`[4, i)` is uncontrolled, so no bridge. -/
theorem RVFXZBU3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (i : ℕ) (p : Equiv.Perm ℕ),
      saturated V → Packing V → barV V 3 ul → permutes p (Set.Icc 0 (i - 1)) →
      (∀ j : ℕ, i ≤ j → p j = j) →
      mcell i V (leftActionList p ul) = mcell i V ul := by
  sorry

/-- `PackingAuto2.LEPJBDJ_concl` (Auto2:767), discharged by
`PackingAuto11.LEPJBDJ` (LEPJBDJ.hl:29).  Shape-verbatim. -/
theorem LEPJBDJ_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V 3 ul → 1 ≤ k → k ≤ 4 → mcell k V ul ≠ ∅ →
      V ∩ mcell k V ul = setOfList (truncateSimplex (k - 1) ul) :=
  fun V ul k hs hp hb h1 h4 hne => LEPJBDJ V ul k hs hp hb h1 h4 hne

/-- `PackingAuto2.LEPJBDJ_0_concl` (Auto2:774), discharged by
`PackingAuto11.LEPJBDJ_0` (LEPJBDJ.hl:34).  Shape-verbatim. -/
theorem LEPJBDJ_0_concl_discharged :
    ∀ (V : Set V3) (ul : List V3), saturated V → Packing V →
      barV V 3 ul → V ∩ mcell 0 V ul = ∅ :=
  fun V ul hs hp hb => LEPJBDJ_0 V ul hs hp hb

/-- `PackingAuto2.HDTFNFZ_concl` (Auto2:779), discharged by
`PackingAuto10.HDTFNFZ`.  Shape-verbatim (implicit binders). -/
theorem HDTFNFZ_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3) (X : Set V3),
      saturated V → Packing V → barV V 3 ul → X = mcell k V ul → ¬nullSet X →
      VX V X = V ∩ X :=
  fun V ul k v X hs hp hb hX hn => @HDTFNFZ V ul k v X hs hp hb hX hn

/-- `PackingAuto2.URRPHBZ1_concl` (Auto2:786), discharged by
`PackingAuto10.URRPHBZ1` (URRPHBZ1.hl:686).  Shape-verbatim. -/
theorem URRPHBZ1_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ), saturated V →
      Packing V → barV V 3 ul → MeasurableSet (mcell k V ul) :=
  fun V ul k hs hp hb => URRPHBZ1 V ul k hs hp hb

/-- `PackingAuto2.URRPHBZ2_concl` (Auto2:791), discharged by
`PackingAuto13.URRPHBZ2`.  Shape-verbatim. -/
theorem URRPHBZ2_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
      saturated V → Packing V → barV V 3 ul → v ∈ V →
      EventuallyRadial v (mcell k V ul) :=
  fun V ul k v hs hp hb hv => URRPHBZ2 V ul k v hs hp hb hv

/-- `PackingAuto2.URRPHBZ3_concl` (Auto2:798), discharged by
`PackingAuto17.URRPHBZ3` (via `hdtfnfz_p17` + `CLOSED_MCELL`).  The twin
is genuinely proved (sorry-free kernel); shape-verbatim. -/
theorem URRPHBZ3_concl_discharged :
    ∀ (V : Set V3) (ul : List V3) (k : ℕ) (v : V3),
      saturated V → Packing V → barV V 3 ul → ¬nullSet (mcell k V ul) →
      v ∈ V \ VX V (mcell k V ul) →
      ∃ t : ℝ, t > 0 ∧ ∀ p ∈ mcell k V ul, t < dist p v :=
  fun V ul k v hs hp hb hn hv => URRPHBZ3 hs hp hb hn hv

/-- `PackingAuto2.QZYZMJC_concl` (Auto2:806), discharged by
`PackingAuto16.QZYZMJC`.  Shape-verbatim. -/
theorem QZYZMJC_concl_discharged :
    ∀ (V : Set V3) (v : V3), saturated V → Packing V → v ∈ V →
      setSum {X | mcellSet V X ∧ v ∈ VX V X} (fun t => sol v t) = 4 * Real.pi :=
  fun V v hs hp hv => QZYZMJC V v hs hp hv

/-- `PackingAuto2.KIZHLTL1_concl` (Auto2:812), discharged by
`PackingAuto16.KIZHLTL1` (KIZHLTL.hl:46).  DELTA BRIDGE: the twin's
conclusion is stated over its public `voronoiOpenP16`, whose body is
identical to Auto2's PRIVATE `voronoiOpen`; the statement here carries
the unfolded body and `exact` closes by delta. -/
theorem KIZHLTL1_concl_discharged :
    ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
      1 ≤ r →
      setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real +
          c * r ^ 2 ≤
        setSum (V ∩ Metric.ball 0 r)
          (fun u => volume.real {x : V3 | ∀ w ∈ V, w ≠ u → dist x u < dist x w}) :=
  KIZHLTL1

/-- `PackingAuto2.KIZHLTL2_concl` (Auto2:820), discharged by
`PackingAuto16.KIZHLTL2` (KIZHLTL.hl:285).  Shape-verbatim. -/
theorem KIZHLTL2_concl_discharged :
    ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
      1 ≤ r →
      ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1 + c * r ^ 2 ≤
        (2 * mm1 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) :=
  KIZHLTL2

/-- `PackingAuto2.KIZHLTL3_concl` (Auto2:828), discharged by
`PackingAuto16.KIZHLTL3`.  Shape-verbatim (NOTE: no HL proof exists for
this general-`f` form anywhere; the twin is sorried, taint flows). -/
theorem KIZHLTL3_concl_discharged :
    ∀ (V : Set V3) (f : ℝ → ℝ), ∃ c : ℝ, ∀ r : ℝ,
      saturated V → Packing V → 1 ≤ r →
      (∃ c1 : ℝ, ∀ x : ℝ, 2 ≤ x ∧ x < Real.sqrt 8 → |f x| ≤ c1) →
      ((8 * mm2 / Real.pi) *
            setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
              (fun X => setSum (edgeX V X) fun e =>
                let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
                dihX V X (q.1, q.2) * f (hl [q.1, q.2]))
          + c * r ^ 2 ≤
        8 * mm2 * setSum (V ∩ Metric.ball 0 r)
          (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v < Real.sqrt 8}
            (fun v => f (hl [u, v])))) :=
  KIZHLTL3

/-- `PackingAuto2.OXLZLEZ_concl` (Auto2:843), discharged by
`PackingAuto25.OXLZLEZ` — THE CAPSTONE wiring.  The twin's kernel
(by_contra → CELL_CLUSTER_ESTIMATE_PROPS → GRHIDFA_concl) is real, but it
is conditional on the two Merge_ineq/Oxl_def bank antecedents
`pack_nonlinear_non_ox3q1h` (PackingAuto21:147) and `ox3q1hP25`
(PackingAuto25:88), both upstream `Prop := sorry` placeholders the
interface does not carry; they are supplied `by sorry` here, so the
reachable debt is exactly the twin's kernel plus the two bank leaves. -/
theorem OXLZLEZ_concl_discharged :
    ∀ V : Set V3, saturated V → Packing V →
      cellClusterInequality V :=
  fun V hs hp => OXLZLEZ V (by sorry) (by sorry) hp hs

/-- `PackingAuto2.UPFZBZM_concl` (Auto2:854), discharged by
`PackingAuto19.UPFZBZM` (UPFZBZM.hl:227).  Shape-verbatim; the twin's
witness is real but leans on the sorried `NEGLIGIBLE_FUNC`/
`FCC_COMPATABILITY_FUNC` pair — taint flows. -/
theorem UPFZBZM_concl_discharged :
    ∀ V : Set V3, saturated V → Packing V →
      cellClusterInequality V → TSKAJXY_statement → lmfunInequality V →
      ∃ G : V3 → ℝ, negligibleFun0 G V ∧ fccCompatible G V :=
  fun V hs hp hcc hT hlm => UPFZBZM V hs hp hcc hT hlm

/-- `PackingAuto2.RDWKARC_concl` (Auto2:860), discharged by
`PackingAuto19.RDWKARC` (RDWKARC.hl).  Shape-verbatim. -/
theorem RDWKARC_concl_discharged :
    ¬keplerConjecture →
    (∀ V : Set V3, Packing V → saturated V → cellClusterInequality V) →
    TSKAJXY_statement →
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V :=
  RDWKARC

/-- `PackingAuto2.GOTCJAH_concl` (Auto2:867).  TWIN MISMATCH:
`PackingAuto22.GOTCJAH` (counting_spheres.hl:4366) is a different
encoding — `fchanged c = WF` vs the interface's
`topologicalComponentYfan` membership, `asn` vs `Real.arcsin`,
`0 ∈ interior P`/`0 < b`/facet-cardinality vs the interface's
nonempty-facet + component + `extremePoints`-card hypotheses.  No bridge
without real geometry; PA22 deliberately not imported. -/
theorem GOTCJAH_concl_discharged :
    ∀ (s : Set V3) (f : Set V3) (v : V3) (b : ℝ) (WF : Set V3)
      (h : ℝ) (k : ℕ), polyhedron s → Bornology.IsBounded s →
      (∃ r : ℝ, r > 0 ∧ Metric.ball 0 r ⊆ s) → FacetOf f s →
      f = {p : V3 | p ⬝ᵥ v = b} ∩ s →
      WF ∈ Kepler.Text.Fan.topologicalComponentYfan 0 (fanOfPolyhedron s).1
        (fanOfPolyhedron s).2 →
      f ∩ WF ≠ ∅ →
      rconeGt 0 v h ⊆ WF →
      k = Nat.card {u : V3 | u ∈ Set.extremePoints ℝ f} →
      2 * Real.pi - 2 * (k : ℝ) * Real.arcsin (h * Real.sin (Real.pi / k)) ≤
        sol 0 WF := by
  sorry

/-- `PackingAuto2.TIWWFYQ_concl` (Auto2:884), discharged by
`PackingAuto5.TIWWFYQ` (pack3.hl:564).  Shape-verbatim. -/
theorem TIWWFYQ_concl_discharged :
    ∀ (V : Set V3) (p : V3), Packing V → saturated V →
      ∃ v : V3, v ∈ V ∧ p ∈ voronoiClosed V v :=
  fun V p hV hs => TIWWFYQ V p hV hs

/-- `PackingAuto2.VORONOI_BALL2_concl` (Auto2:889), discharged by
`PackingAuto5.VORONOI_BALL2` (pack3.hl:767).  Shim: the twin needs only
`saturated V`; the interface's `Packing V` and `v ∈ V` are discarded. -/
theorem VORONOI_BALL2_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V → v ∈ V →
      voronoiClosed V v ⊆ Metric.ball v 2 :=
  fun V v _ hs _ => VORONOI_BALL2 V v hs

/-- `PackingAuto2.VORONOI_INTER_BIS_LE_concl` (Auto2:894), discharged by
`PackingAuto5.VORONOI_INTER_BIS_LE` (pack3.hl:823).  Shape-verbatim
(twin is sorried; taint flows). -/
theorem VORONOI_INTER_BIS_LE_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      v ∈ V →
      voronoiClosed V v =
        ⋂₀ ((fun u : V3 => bisLe v u) ''
          {u : V3 | u ∈ V ∧ u ∈ Metric.ball v 4 ∧ u ≠ v}) :=
  fun V v hV hs hv => VORONOI_INTER_BIS_LE V v hV hs hv

/-- `PackingAuto2.VORONOI_POLYHEDRON_concl` (Auto2:902), discharged by
`PackingAuto5.VORONOI_POLYHEDRON` (pack3.hl:916; sorried — taint
flows). -/
theorem VORONOI_POLYHEDRON_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      v ∈ V → polyhedron (voronoiClosed V v) :=
  fun V v hV hs hv => VORONOI_POLYHEDRON V v hV hs hv

/-- `PackingAuto2.DRUQUFE_concl` (Auto2:913), discharged by
`PackingAuto5.DRUQUFE` (pack3.hl:970).  Shape-verbatim. -/
theorem DRUQUFE_concl_discharged :
    ∀ (V : Set V3) (v : V3), Packing V → saturated V →
      IsCompact (voronoiClosed V v) ∧ Convex ℝ (voronoiClosed V v) ∧
        MeasurableSet (voronoiClosed V v) :=
  DRUQUFE

/-- `PackingAuto2.KHEJKCI_concl` (Auto2:919), discharged by
`PackingAuto6.KHEJKCI` (Rogers.hl:142) — shim: the interface's
`vorList V k ul` is `barV V k ul ∧ hl ul < sqrt 2` (Auto2:278), and the
twin needs only the `.1` conjunct. -/
theorem KHEJKCI_concl_discharged :
    ∀ (V : Set V3) (k : ℕ) (ul : List V3), saturated V →
      Packing V → vorList V k ul →
      FaceOf (voronoiList V ul) (voronoiClosed V (hdV ul)) :=
  fun V k ul hs hp hv => KHEJKCI V k ul hs hp hv.1

/-- `PackingAuto2.GRUTOTI1_concl` (Auto2:926), also mirrored by the
PRIVATE `PackingAuto24.GRUTOTI1_concl_p24` statement-copy.  NO
REACHABLE TWIN: the only downstream carrier is that PRIVATE copy, which
no other module can name; PA25 consumes the interface itself
(`LEAF_RANK_GRUTOTI` lane) rather than proving it. -/
theorem GRUTOTI1_concl_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3), saturated V →
      Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 → hl [u0, u1] < Real.sqrt 2 →
      e = {u0, u1} →
      setSum {X | mcellSet V X ∧ e ∈ edgeX V X} (fun t => dihX V t (u0, u1)) =
        2 * Real.pi := by
  sorry

/-- `PackingAuto2.REUHADY_concl` (Auto2:935), discharged by
`PackingAuto24.REUHADY_p24` (REUHADY.hl) — statement-identical
(discharge candidate marked at the PA24 copy; sorried — taint flows). -/
theorem REUHADY_concl_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (v1 v2 : V3)
      (e : Set V3) (w1 w2 : V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
      e = {u0, u1} → ¬(azim u0 u1 w1 w2 = 0) →
      hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
      barV V 2 vl1 ∧ barV V 2 vl2 →
      setOfList (truncateSimplex 1 vl1) = e ∧
      setOfList (truncateSimplex 1 vl2) = e ∧
      v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
        X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
      setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
        azim u0 u1 v1 v2 :=
  REUHADY_p24

/-- `PackingAuto2.REUHADY_concl_version2` (Auto2:953), discharged by
`PackingAuto24.REUHADY_version2_p24` — statement-identical (sorried —
taint flows). -/
theorem REUHADY_concl_version2_discharged :
    ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
      (v1 v2 : V3) (e : Set V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
      e = {u0, u1} →
      wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
        affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} →
      hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
      barV V 2 vl1 ∧ barV V 2 vl2 →
      setOfList (truncateSimplex 1 vl1) = e ∧
      setOfList (truncateSimplex 1 vl2) = e ∧
      v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
        X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
      setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
        azim u0 u1 v1 v2 :=
  REUHADY_version2_p24

/-! ## Auto3 `OXLZLEZ1.hl` family — blocked in a parallel encoding

All nine interfaces live over `PackingAuto3.CcV11`.  The only downstream
carrier of the matching HL statements is `PackingAuto4`'s OXLZLEZ2 wave,
whose twins (`CHQSQEY`, `MTMLSRF`, `LXDEYBO`, `UNPNFVW`, `IPVICGW`,
`RSIWAMP`, `UTEOITF`, `LUIKGMH`, `GRHIDFA`) are stated over a PRIVATE
`structure CC4P4` with private accessors — a parallel encoding of the
same HL content.  Neither the type nor the property constants are
referable outside PA4, so no `exact` can even be written; PA4 is
deliberately not imported.  (PA25's cc-block consumes these interfaces
via `cc_data_v8`, it does not prove them.) -/

/-- `PackingAuto3.CHSQSQEY_concl` (OXLZLEZ1.hl:135).  缺可引用 twin：
PackingAuto4 的同名 twin 为私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem CHQSQEY_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) := by
  sorry

/-- `PackingAuto3.MTMLSRF_concl` (OXLZLEZ1.hl:138).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem MTMLSRF_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1) := by
  sorry

/-- `PackingAuto3.LXDEYBO_concl` (OXLZLEZ1.hl:142).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem LXDEYBO_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_4cell_v11 cc) ≤ 4 := by
  sorry

/-- `PackingAuto3.UNPNFVW_concl` (OXLZLEZ1.hl:145).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem UNPNFVW_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_qy_v11 cc) ≤ 1 := by
  sorry

/-- `PackingAuto3.IPVICGW_concl` (OXLZLEZ1.hl:156).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem IPVICGW_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_small_v11 cc i := by
  sorry

/-- `PackingAuto3.RSIWAMP_concl` (OXLZLEZ1.hl:159).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem RSIWAMP_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_card_v11 cc ≤ 4 := by
  sorry

/-- `PackingAuto3.UTEOITF_concl` (OXLZLEZ1.hl:167).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem UTEOITF_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_4cell_v11 cc i := by
  sorry

/-- `PackingAuto3.LUIKGMH_concl` (OXLZLEZ1.hl:170).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。 -/
theorem LUIKGMH_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    4 ≤ cc_card_v11 cc := by
  sorry

/-- `PackingAuto3.GRHIDFA_concl` (OXLZLEZ1.hl:173).  缺可引用 twin：
PackingAuto4 私有 CC4P4 平行编码，上游模块 PackingAuto4。（PA25.OXLZLEZ
的 kernel 在等价的 v11 数据上消费本条目。） -/
theorem GRHIDFA_concl_discharged (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    False := by
  sorry

-- Self-checks.  Ground truth = `#print axioms`, not prose:
--  * the first three are the sorry-free discharges of the previous wave
--    (expect exactly `[propext, Classical.choice, Quot.sound]`);
--  * the wired entries below are EXPECTED to list `sorryAx` — that is the
--    honest reachable-debt expansion (taint flows through the twins /
--    bank placeholders).
#print axioms EMNWUUS1_concl_discharged
#print axioms VORONOI_BALL2_concl_discharged
#print axioms DRUQUFE_concl_discharged
#print axioms OXLZLEZ_concl_discharged
#print axioms REUHADY_concl_discharged
#print axioms REUHADY_concl_version2_discharged
#print axioms URRPHBZ3_concl_discharged

end Kepler.Text

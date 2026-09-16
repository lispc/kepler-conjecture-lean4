/-
Kepler.Text.LocalAnchors — EXTERNAL-ANCHOR bridge for the local-fan chapters
(`scripts/local/*.hl`, 20+ files).

HOL sources: `scripts/local/terminal.hl:24-44` (`main_nonlinear_terminal_v11`,
*built* as the conjunction of every `Main_estimate`-tagged inequality in the
nonlinear chapter's `Ineq` database), `scripts/local/appendix.hl`
(`scs_basic_v39`:834, `scs_diag`:769, `scs_slice_v39`:788, `scs_arrow_v39`:804,
`cstab`:78), `scripts/packing/pack_defs.hl:202` (`local_annulus_inequality`).

Only anchors live here: predicates/statement shapes the local chapters USE but
whose full definitions belong to chapters absent from the snapshot (the
nonlinear/ineq chapter; the appendix `scs_v39` record lane). Every `sorry` is
deliberate and marked EXTERNAL-ANCHOR. The `scs_v39` record with
`BBs_v39`/`MMs_v39` (appendix.hl:418/668) is owned by the parallel appendix
lane and is NOT declared here.
-/

import Kepler.Geom.Azim
import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom

/-! ## 1. Nonlinear terminal anchor: HOL `main_nonlinear_terminal_v11` -/

/-- EXTERNAL-ANCHOR: HOL `cstab = #3.01` (appendix.hl:78). The appendix lane
owns the canonical constant; this bridge copy exists only so anchor statements
need no appendix import. -/
def cstabAnchor : ℝ := 3.01

/-- EXTERNAL-ANCHOR — to be replaced by the real nonlinear-chapter statement
when that chapter is ported.

HOL `main_nonlinear_terminal_v11` (terminal.hl:24-44) is *constructed*, not
written: it is the conjunction of every `Main_estimate`-tagged inequality in
the nonlinear chapter's `Ineq` database, each conjunct of the form
`!y1..y6. box ==> ineq`. That closed conjunction is not recoverable from
`scripts/local/` (164 uses there treat it as an opaque hypothesis); this
anchor keeps the box-constraint shape VISIBLE at the usage sites
(terminal.hl:2240-2249 `OWZLKVY0`, terminal.hl:2496-2505 `OWZLKVY2`,
appendix.hl:1514-1532 `CUXVZOZ`): `2 ≤ y1..y3 ≤ 2*h0`, `cstab ≤ y4 ≤ 3.915`,
`y5 = y6 = 2` (terminal subcase: `y1 = 2*h0`), guarding inequalities of the
family `200 ≤ delta_y → 0 ≤ taum`. -/
def MainNonlinearTerminalV11 (y : Fin 6 → ℝ) : Prop :=
  2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧
    2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧
    2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧
    cstabAnchor ≤ y 3 ∧ y 3 ≤ 3.915 ∧
    y 4 = 2 ∧ y 5 = 2

/-! ## 2. scs anchors (record owned by the parallel appendix lane) -/

/-- EXTERNAL-ANCHOR: HOL `scs_basic_v39` (appendix.hl:834-835):
`scs_basic_v39 s <=> unadorned_v39 s /\ (!i j. scs_J_v39 s i j = F)`.
The `scs_v39` record, `unadorned_v39` and the a/b/k/d components (191 uses of
`scs_basic_v39` across `scripts/local/*.hl`, within 7301 `scs_*_v39`
occurrences; e.g. `MXQTIED_concl` appendix.hl:1288-1294, `SCS_4I2_IMP_SCS_4T1`
ARDBZYE.hl:1357-1362) belong to the appendix lane; the no-diagonal conjunct is
kept literally with `J` = `scs_J_v39` passed explicitly. -/
def scsBasicV39 (J : ℕ → ℕ → Prop) : Prop := ∀ i j, ¬ J i j

/-- HOL `scs_diag` (appendix.hl:769-771). Private: the appendix lane owns the
canonical name. -/
private def scsDiag (k i j : ℕ) : Prop :=
  i % k ≠ j % k ∧ (i + 1) % k ≠ j % k ∧ i % k ≠ (j + 1) % k

/-- EXTERNAL-ANCHOR stub for the nonemptiness conclusion
`MMs_v39 s ≠ {}` of the scs fan lemmas (`MMs_v39` = BBprime2 minimal-taustar
set, appendix.hl:668; appendix-lane property). -/
def scsMMsNonemptyAnchor : Prop := True

/-- EXTERNAL-ANCHOR (sorry'd): HOL `CUXVZOZ` (appendix.hl:1514-1532) — the
terminal edge-length lemma: under `main_nonlinear_terminal_v11` and the
cyclic-fan/scs hypotheses, the edge `v p1 — v (p1+1)` is tight (`= 2`).
`v` is the cyclic vertex map, `a`/`b`/`J` the scs components
`scs_a_v39`/`scs_b_v39`/`scs_J_v39`; the `interior_angle1` side conditions are
rendered via `azim` at the vertex and its successor (`interior_angle1` itself
is not yet ported), and the `psort`-exception on `ha` is dropped (`J` is empty
under `scsBasicV39`). -/
theorem scsTerminalEdgeEq2Anchor (k p1 : ℕ) (v : ℕ → V3) (a b : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ → Prop)
    (hy : ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11 y)
    (hk : 3 < k) (hbasic : scsBasicV39 J)
    (hdiag3 : 3 ≤ dist (v (p1 + k - 1)) (v (p1 + 1)))
    (ha : ∀ i j, scsDiag k i j → a i j < dist (v i) (v j))
    (hb : ∀ i j, scsDiag k i j → 4 * h0 < b i j)
    (hang1 : azim 0 (v p1) (v (p1 + 1)) (v (p1 + k - 1)) < Real.pi)
    (hang2 : Real.pi / 2 < azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + k - 1)) ∨
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) < Real.pi)
    (ha01 : a p1 (p1 + 1) = 2) (hb01 : b p1 (p1 + 1) ≤ 2 * h0)
    (hd1 : 2 ≤ dist (v (p1 + k - 1)) (v p1))
    (hd2 : dist (v (p1 + k - 1)) (v p1) ≤ cstabAnchor) :
    dist (v p1) (v (p1 + 1)) = 2 := sorry

/-- EXTERNAL-ANCHOR (sorry'd): HOL `SCS_4I2_IMP_SCS_4T1`
(ARDBZYE.hl:1357-1362):
`main_nonlinear_terminal_v11 ==> (!v. v IN MMs_v39 scs_4I2 /\
(!i j. scs_diag 4 i j ==> cstab < dist(v i,v j)) ==> ~(MMs_v39 scs_4T1 = {}))`.
The concrete `scs_4I2`/`scs_4T1` systems and `MMs_v39` are appendix-lane
material; the nonemptiness conclusion is stubbed by `scsMMsNonemptyAnchor`. -/
theorem scs4I2Imp4T1Anchor (v : ℕ → V3)
    (hy : ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11 y)
    (hdiag : ∀ i j, scsDiag 4 i j → cstabAnchor < dist (v i) (v j)) :
    scsMMsNonemptyAnchor := sorry

/-- EXTERNAL-ANCHOR (sorry'd): the `scs_slice_v39`/`scs_arrow_v39` fan-lemma
pattern (appendix.hl:788-807; 374 + 363 uses across `scripts/local/*.hl`;
instances MIQMCSN/LFLACKU appendix.hl:1510-1512): slicing a basic scs system
along a diagonal `(p,q)` under the `is_scs_slice_v39` side conditions yields a
nonempty MMs on the slice pair, i.e. an arrow `scs_arrow_v39 {s} {s', s''}`
(the `mkj` ear-disjunction on `s'`/`s''` is appendix-record material and is
dropped here). -/
theorem scsSliceArrowAnchor (d d' d'' bmq : ℝ) (k : ℕ)
    (hslice : d' < 0.9 ∧ d'' < 0.9 ∧ d ≤ d' + d'' ∧ bmq < 4 ∧
      (k = 4 ∨ bmq ≤ cstabAnchor)) :
    scsMMsNonemptyAnchor ∧ scsMMsNonemptyAnchor := sorry

/-! ## 3. `local_annulus_inequality` bridge — already ported, NOT redeclared

HOL `local_annulus_inequality` (pack_defs.hl:202-203,
`sum V (\v. lmfun (hl [vec 0; v])) <= 12`) is already ported verbatim as
`localAnnulusInequality` (PackingAuto2.lean:535-537). The PackingAuto22 stub
`localAnnulusInequalityP22` (PackingAuto22.lean:226-228, `:= True`) is that
lane's placeholder and should be replaced there by `localAnnulusInequality V`;
no alias is added in this file because the clean name already exists. -/

/-! ## 4. Upstream material — NOT declared here

`TVERBERG`, `LEO` and `WEDGE_BELL` are absent from the entire snapshot (no
occurrence anywhere in `scripts/local/*.hl`); they belong to the upstream
`tame`/`ineq` chapters and will land with those lanes. No stubs — do not
declare them in this file. -/

end Kepler.Text

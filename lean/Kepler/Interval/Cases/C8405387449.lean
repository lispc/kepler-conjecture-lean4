/-
  Kepler.Interval.Cases.C8405387449 — lane c840-swap-prep-w1 (2026-11-20),
  execution template for the structured swap of case prep-8405387449
  (HOL Main_estimate 8405387449, main_estimate_ineq.hl:1180:
  `4·x1_delta_y < 3.86·delta4_squared_y ∨ delta_y < 0`,
  tan2lower = #3.86 = 193/50; the `dih_y < 1.1` disjunct linearized).

  Old face: 497 shards / 40,785 kernel-decide leaves / 92,064 lines
  (BBTreeD replay tree, bb_arb prec 64).  Machine-checked facts that
  collapse it to a single certificate:

  * all 40,785 leaves select goal index 0 (the `(193/50)·deltaX4² −
    4·x1·deltaX > 0` disjunct) — zero leaves use the `delta_y < 0`
    disjunct, so the disjunction is witnessed by the first goal on the
    whole box;
  * the registry pins y1 = y4 = 2, so x1 = x4 = 4 on the whole box
    (all 81,074 node/leaf boxes carry [4,4] on slots 0 and 3).

  New face: one 81-coefficient pinned Bernstein certificate
  (CertP840.lean, emitted): on x2, x3 in [4, 213084065/2^25], x5 in
  [9728208299/2^30, 13531831337/2^30], x6 in [6818690079/2^30,
  2432052075/2^28], the exact Bernstein tensor (multidegree
  (2,2,2,2)) is strictly positive with min coefficient
  352.4177168373... (exact Fraction, cross-checked by 16-corner exact
  enumeration, 2000 random rational points, edge/center sweep and a
  200k-point float64 grid).

  Statements NOT touched: `C8405387449_pos` below keeps the old
  docstring, binder and conclusion lines byte-equal; only the proof
  body after `:= by` changes.  `Base.lean` is byte-identical and not
  part of the swap.  The sole consumer `T11Proofs.lean` (:21 import,
  :116-173 glue incl. the private eval identity re-proved verbatim
  below) needs zero changes.

  No sorry, no native_decide, no new axioms: the certificate is pure
  peel2 ring arithmetic (P0 CertA/CertD/CertP machinery), and the old
  BBTreeD/splitOKB kernel-decide layer is retired with the tree.
-/
import Kepler.Interval.Cases.C8405387449.Base
import Kepler.Interval.Cases.C8405387449.CertP840
import Kepler.Text.SphereKit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

open Kepler.Text

/-! ## The eval identity

Verbatim copy of the in-tree proven script `T11Proofs.lean:116-123`
(private there, same-shape module-private here; P0's bridge did the
same for the `A2QITNPEAGlue` identity). -/

set_option maxHeartbeats 2000000 in
private theorem eval_C8405387449 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C8405387449Expr).evalReal ρ
      = -(4 * (ρ 0 * deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5))
          + (-193 / 50 : ℝ) * (deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) ^ 2) := by
  dsimp only [Kepler.Interval.Cases.C8405387449Expr, IExpr.evalReal, deltaX, deltaX4]
  simp only [Dyadic.toReal_def]
  norm_num
  ring

/-! ## End-to-end theorem -/

/-- End-to-end: some disjunct holds at every point of the box. -/
theorem C8405387449_pos (ρ : Fin 6 → ℝ) (hρ : boxMem C8405387449Box ρ) :
    ∃ g ∈ C8405387449Goals, g.eval ρ := by
  -- pinned slots: the registry fixes y1 = y4 = 2, i.e. x1 = x4 = 4
  -- (box slots 0 and 3 are the point interval [4, 4]).
  have hlit4 : Dyadic.toReal ⟨4, 0⟩ = (4:ℝ) := by
    simp only [Dyadic.toReal_def]; norm_num
  have h0 : ρ 0 = (4:ℝ) := by
    have hl : Dyadic.toReal ⟨4, 0⟩ ≤ ρ 0 := (hρ 0).1
    have hh : ρ 0 ≤ Dyadic.toReal ⟨4, 0⟩ := (hρ 0).2
    rw [hlit4] at hl hh
    exact le_antisymm hh hl
  have h3 : ρ 3 = (4:ℝ) := by
    have hl : Dyadic.toReal ⟨4, 0⟩ ≤ ρ 3 := (hρ 3).1
    have hh : ρ 3 ≤ Dyadic.toReal ⟨4, 0⟩ := (hρ 3).2
    rw [hlit4] at hl hh
    exact le_antisymm hh hl
  -- live-coordinate bounds (dyadic endpoints, reduced rationals)
  have hx2l : (4:ℝ) ≤ ρ 1 := by
    have h : Dyadic.toReal ⟨4, 0⟩ ≤ ρ 1 := (hρ 1).1
    rwa [hlit4] at h
  have hx2h : ρ 1 ≤ ((213084065/33554432:ℝ)) := by
    have h : ρ 1 ≤ Dyadic.toReal ⟨213084065, -25⟩ := (hρ 1).2
    have hlit : Dyadic.toReal ⟨213084065, -25⟩ = ((213084065/33554432:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  have hx3l : (4:ℝ) ≤ ρ 2 := by
    have h : Dyadic.toReal ⟨4, 0⟩ ≤ ρ 2 := (hρ 2).1
    rwa [hlit4] at h
  have hx3h : ρ 2 ≤ ((213084065/33554432:ℝ)) := by
    have h : ρ 2 ≤ Dyadic.toReal ⟨213084065, -25⟩ := (hρ 2).2
    have hlit : Dyadic.toReal ⟨213084065, -25⟩ = ((213084065/33554432:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  have hx5l : ((9728208299/1073741824:ℝ)) ≤ ρ 4 := by
    have h : Dyadic.toReal ⟨9728208299, -30⟩ ≤ ρ 4 := (hρ 4).1
    have hlit : Dyadic.toReal ⟨9728208299, -30⟩ = ((9728208299/1073741824:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  have hx5h : ρ 4 ≤ ((13531831337/1073741824:ℝ)) := by
    have h : ρ 4 ≤ Dyadic.toReal ⟨13531831337, -30⟩ := (hρ 4).2
    have hlit : Dyadic.toReal ⟨13531831337, -30⟩ = ((13531831337/1073741824:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  have hx6l : ((6818690079/1073741824:ℝ)) ≤ ρ 5 := by
    have h : Dyadic.toReal ⟨6818690079, -30⟩ ≤ ρ 5 := (hρ 5).1
    have hlit : Dyadic.toReal ⟨6818690079, -30⟩ = ((6818690079/1073741824:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  have hx6h : ρ 5 ≤ ((2432052075/268435456:ℝ)) := by
    have h : ρ 5 ≤ Dyadic.toReal ⟨2432052075, -28⟩ := (hρ 5).2
    have hlit : Dyadic.toReal ⟨2432052075, -28⟩ = ((2432052075/268435456:ℝ)) := by
      simp only [Dyadic.toReal_def]; norm_num
    rwa [hlit] at h
  -- witness the first goal: the pinned Bernstein certificate.
  refine ⟨DisjGoal.pos C8405387449Expr, ?_, ?_⟩
  · exact List.Mem.head _
  · show 0 < (C8405387449Expr).evalReal ρ
    rw [eval_C8405387449, h0, h3]
    have hcert := Kepler.Interval.Cases.C8405387449.CertP840.certP840_pos
      (ρ 1) (ρ 2) (ρ 4) (ρ 5) hx2l hx2h hx3l hx3h hx5l hx5h hx6l hx6h
    linarith

#print axioms C8405387449_pos

end Kepler.Interval.Cases

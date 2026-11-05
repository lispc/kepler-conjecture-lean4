/-
Kepler.Text.Gamma4WideBanks — lane `nli-rest-b2`, part 4: the per-bank
**main-branch interfaces** for the 11 banks whose refined-corner scan has a
single uniform positive branch.

For each bank the theorem below reduces the full bank proposition (a
6-variable `∀` over the bank box with the disjunction of branches) to the
single **main-branch inequality on the whole box**.  That is the exact
residual obligation of the corner route: once a wave proves
`∀ y ∈ box, 0 < main y`, the bank follows with no further case analysis.
The box predicate is spelled out separately so the analytic statement is
visible.

The three remaining banks (`QITNPEA5400790175a`, `FHBVYXZa`, `FHBVYXZv2a`)
have no uniform branch: at the refined corners their main branch dips
(`−7.27e−3`, `−5.56e−3`, `−1.13e−2`) while `rad2 > 2` and `η² < 1.34²` each
fail somewhere else, so they need the branch-switching analysis documented
in `Evidence.md` (they are deliberately not reduced here, to avoid hiding a
case split behind a false uniform premise).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.PackingAuto21
import Kepler.Text.Gamma4WideD
import Kepler.Text.Gamma4WideKink

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## The bank boxes -/

/-- `[2hmin,2hplus]×[2,2hmin]⁵`. -/
def g4wB5 (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 ≤ y2 ∧ y2 ≤ 2 * hminus ∧
    2 ≤ y3 ∧ y3 ≤ 2 * hminus ∧ 2 ≤ y4 ∧ y4 ≤ 2 * hminus ∧
    2 ≤ y5 ∧ y5 ≤ 2 * hminus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hminus

/-- `[2hmin,2hplus]×[2,2hmin]³×[2hmin,√8]×[2,2hmin]²`. -/
def g4wBy4 (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 ≤ y2 ∧ y2 ≤ 2 * hminus ∧
    2 ≤ y3 ∧ y3 ≤ 2 * hminus ∧ 2 * hminus ≤ y4 ∧ y4 ≤ Real.sqrt 8 ∧
    2 ≤ y5 ∧ y5 ≤ 2 * hminus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hminus

/-- `[2hmin,2hplus]×[2,2hmin]³×[2hplus,√8]×[2,2hmin]²`. -/
def g4wBy4hi (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 ≤ y2 ∧ y2 ≤ 2 * hminus ∧
    2 ≤ y3 ∧ y3 ≤ 2 * hminus ∧ 2 * hplus ≤ y4 ∧ y4 ≤ Real.sqrt 8 ∧
    2 ≤ y5 ∧ y5 ≤ 2 * hminus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hminus

/-- `[2hmin,2hplus]²×[2,2hmin]×[2hmin,2hplus]×[2,2hmin]²`. -/
def g4wBcrit (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 * hminus ≤ y2 ∧ y2 ≤ 2 * hplus ∧
    2 ≤ y3 ∧ y3 ≤ 2 * hminus ∧ 2 * hminus ≤ y4 ∧ y4 ≤ 2 * hplus ∧
    2 ≤ y5 ∧ y5 ≤ 2 * hminus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hminus

/-! ## `QITNPEA 5400790175 b` (main = `γ4/2 + β_lb + γ3f > 0.0057`) -/

theorem nliRestQITNPEA5400790175b_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wBy4 y1 y2 y3 y4 y5 y6 →
      0.0057 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpLb +
        gamma3f y1 y2 y6 (Real.sqrt 2) lmfun) :
    bank_QITNPEA5400790175b := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## `QITNPEA 3848804089` (main = `γ4 − 0.161517 + 0.119482·dihY > 0`) -/

theorem nliRestQITNPEA3848804089_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.161517 +
        0.119482 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA3848804089 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩

/-! ## `QITNPEA 5814748276` (main = `γ4 − 0.00127562 + 0.00522841·dihY > 0`) -/

theorem nliRestQITNPEA5814748276_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.00127562 +
        0.00522841 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA5814748276 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩

/-! ## `QITNPEA 6206775865` (main = `γ4 + 0.0142852 − 0.00609451·dihY > 0`) -/

theorem nliRestQITNPEA6206775865_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.0142852 -
        0.00609451 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA6206775865 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩

/-! ## `QITNPEA 5653753305` (main = `γ4 + 0.0659 − 0.042·dihY > 0`) -/

theorem nliRestQITNPEA5653753305_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun + 0.0659 -
        0.042 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA5653753305 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩

/-! ## `BIXPCGW 9455898160` (main = `γ4 > −0.00569`) -/

theorem nliRestBIXPCGW9455898160_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      -0.00569 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun) :
    bank_BIXPCGW9455898160 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩

/-! ## `FHBVYXZ b` (main = `γ4 + γ3f > 0`) -/

theorem nliRestFHBVYXZb_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun +
        gamma3f y1 y2 y6 (Real.sqrt 2) lmfun) :
    bank_FHBVYXZb := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## `QITNPEA 2134082733` (main = `γ4/2 + β_lb − 0.213849 + 0.119482·dihY > 0`) -/

theorem nliRestQITNPEA2134082733_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wBy4 y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 2 + betaBumpLb - 0.213849 +
        0.119482 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA2134082733 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## `QITNPEA 9939613598` (main = `γ4 − 0.00457511 − 0.00609451·dihY > 0`) -/

theorem nliRestQITNPEA9939613598_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wBy4hi y1 y2 y3 y4 y5 y6 →
      0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun - 0.00457511 -
        0.00609451 * dihY y1 y2 y3 y4 y5 y6) :
    bank_QITNPEA9939613598 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## `BIXPCGW 7274157868 a` (main = `γ4 > 0.0057`) -/

theorem nliRestBIXPCGW7274157868a_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wBy4hi y1 y2 y3 y4 y5 y6 →
      0.0057 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun) :
    bank_BIXPCGW7274157868a := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## `GLFVCVK4 y4crit` (main = `γ4/3 > 0.0057`) -/

theorem nliRestGLFVCVK4y4crit_of_main
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wBcrit y1 y2 y3 y4 y5 y6 →
      0.0057 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / 3) :
    bank_GLFVCVK4y4crit := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  exact Or.inl (h y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h,
    h5l, h5h, h6l, h6h⟩)

/-! ## Axiom audit (house style) -/

#print axioms nliRestQITNPEA5400790175b_of_main
#print axioms nliRestQITNPEA3848804089_of_main
#print axioms nliRestQITNPEA5814748276_of_main
#print axioms nliRestQITNPEA6206775865_of_main
#print axioms nliRestQITNPEA5653753305_of_main
#print axioms nliRestBIXPCGW9455898160_of_main
#print axioms nliRestFHBVYXZb_of_main
#print axioms nliRestQITNPEA2134082733_of_main
#print axioms nliRestQITNPEA9939613598_of_main
#print axioms nliRestBIXPCGW7274157868a_of_main
#print axioms nliRestGLFVCVK4y4crit_of_main

end Kepler.Text

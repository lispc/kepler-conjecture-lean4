/-
Kepler.Text.TaylorSecond.W1DC15873 — lane `wt1-emission-pilot-w1` (2026-11-25).

**DC-only tree certificate** of the wt1 box `15873/RRLLRL#1` (mode `zero`):
the full 152-node tree of `w1F3Z` emitted as `DCJet` chains via
`Kepler.Text.TaylorSecond.DCJet`, in two passes

  * box pass  `Box.J…`  : `JetMem J… f… D`   on `D = {x | I4.mem (x 0) ∧ …}`,
  * point pass `Pt.J…`  : `JetMem J… f… Dpt` on the degenerate `Dpt = {x | x = c}`,

and the T2 terminal `dcT2_pos` with `V := Pt.JTop.value`, `G i := Box.JTop.part i`.

**`dSqrt` repair (M7).**  `Nat.sqrt` does not reduce in the kernel, so no
`decide`/`rfl` may ever see a `dSqrt` node.  Every square root is emitted as a
literal proved through `DCSqrtLit.dSqrt_val` (two `Nat` bracketing facts), and
every node gets a literal equality proved one op at a time
(`dMul ⟨…⟩ ⟨…⟩ = ⟨…⟩` by `rfl`), so the kernel evaluates at most one `DC` op
per node.  The gates are `by rw [ev_…]; decide` on literals.

The slack is decided on ℤ and cast to ℝ (`dcSlack`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.TaylorSecond.LeafKit
import Kepler.Text.TaylorSecond.DCSqrtLit
import Kepler.NliBanks21

set_option maxHeartbeats 32000000
set_option maxRecDepth 2000000
set_option exponentiation.threshold 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DC15873

open DCKit
open DCJetKit
open DCMatan
open DCSqrtLit
open Kepler.Text

noncomputable section

/-! ## 0. The box, centre, half-width, and the two domains -/

def I4 : DC := ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩
def I5 : DC := ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩
def I6 : DC := ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩

/-- The box. -/
def D : Set (Fin 3 → ℝ) :=
  {x | I4.mem (x 0) ∧ I5.mem (x 1) ∧ I6.mem (x 2)}

def s : ℝ := (2 : ℝ) ^ (-(200 : ℤ))
def s2 : ℝ := (2 : ℝ) ^ (-(201 : ℤ))

def c0 : ℝ := ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) + (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ)) * s2
def c1 : ℝ := ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) + (((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) : ℝ)) * s2
def c2 : ℝ := ((((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) : ℝ) + (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ)) * s2

def w0 : ℝ := ((((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) - (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ)) * s2
def w1 : ℝ := ((((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) : ℝ) - (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ)) * s2
def w2 : ℝ := ((((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) - (((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) : ℝ)) * s2

/-- The box widths, in grid units of `2^-200`. -/
def wz0 : ℤ := ((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) - ((4049483871532655494365744472699729758355951544332637944959467 : ℤ))
def wz1 : ℤ := ((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) - ((3657176895331534926107553882173950532625280555789666908403972 : ℤ))
def wz2 : ℤ := ((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) - ((3697021906849702090774160988178878465989773336804422257896241 : ℤ))

def c : Fin 3 → ℝ
  | 0 => c0
  | 1 => c1
  | 2 => c2

def w : Fin 3 → ℝ
  | 0 => w0
  | 1 => w1
  | 2 => w2

/-- The degenerate centre box. -/
def Dpt : Set (Fin 3 → ℝ) := {x | x = c}


theorem s_pos : 0 < s := zpow_pos (by norm_num) _
theorem s2_pos : 0 < s2 := zpow_pos (by norm_num) _
theorem s_eq : s = 2 * s2 := by norm_num [s, s2]

theorem c_mem : c ∈ D := by
  have h4 : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) := by
    exact_mod_cast (by decide : (4049483871532655494365744472699729758355951544332637944959467 : ℤ) ≤ (4049483871533651860230706817030176796531686758792705811703733 : ℤ))
  have h5 : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) := by
    exact_mod_cast (by decide : (3657176895331534926107553882173950532625280555789666908403972 : ℤ) ≤ (3734842111502011420851541171028160066896758316960222749146863 : ℤ))
  have h6 : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) := by
    exact_mod_cast (by decide : (3697021906849702090774160988178878465989773336804422257896241 : ℤ) ≤ (3786260064126602103902664808873744373940916659619106874140858 : ℤ))
  have h4s : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s :=
    mul_le_mul_of_nonneg_right h4 s_pos.le
  have h5s : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s :=
    mul_le_mul_of_nonneg_right h5 s_pos.le
  have h6s : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s :=
    mul_le_mul_of_nonneg_right h6 s_pos.le
  refine ⟨?_, ?_, ?_⟩
  · change ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ c0 ∧ c0 ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s
    simp only [c0]; rw [s_eq] at *; constructor <;> linarith
  · change ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ c1 ∧ c1 ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s
    simp only [c1]; rw [s_eq] at *; constructor <;> linarith
  · change ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ c2 ∧ c2 ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s
    simp only [c2]; rw [s_eq] at *; constructor <;> linarith

theorem seg_mem : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (fun i => c i + t * (x i - c i)) ∈ D := by
  intro x hx t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hc := c_mem
  have hx1 : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ x 0 := hx.1.1
  have hx2 : x 0 ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s := hx.1.2
  have hx3 : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ x 1 := hx.2.1.1
  have hx4 : x 1 ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s := hx.2.1.2
  have hx5 : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ x 2 := hx.2.2.1
  have hx6 : x 2 ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s := hx.2.2.2
  have hc1 : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ c0 := hc.1.1
  have hc2 : c0 ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s := hc.1.2
  have hc3 : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ c1 := hc.2.1.1
  have hc4 : c1 ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s := hc.2.1.2
  have hc5 : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ c2 := hc.2.2.1
  have hc6 : c2 ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s := hc.2.2.2
  rw [s_eq] at hx1 hx2 hx3 hx4 hx5 hx6 hc1 hc2 hc3 hc4 hc5 hc6
  have ht0' : 0 ≤ 1 - t := by linarith
  refine ⟨?_, ?_, ?_⟩
  · change ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ c0 + t * (x 0 - c0) ∧
      c0 + t * (x 0 - c0) ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s
    rw [s_eq]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hc1 ht0', mul_le_mul_of_nonneg_left hx1 ht0]
    · nlinarith [mul_le_mul_of_nonneg_left hc2 ht0', mul_le_mul_of_nonneg_left hx2 ht0]
  · change ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ c1 + t * (x 1 - c1) ∧
      c1 + t * (x 1 - c1) ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s
    rw [s_eq]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hc3 ht0', mul_le_mul_of_nonneg_left hx3 ht0]
    · nlinarith [mul_le_mul_of_nonneg_left hc4 ht0', mul_le_mul_of_nonneg_left hx4 ht0]
  · change ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ c2 + t * (x 2 - c2) ∧
      c2 + t * (x 2 - c2) ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s
    rw [s_eq]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hc5 ht0', mul_le_mul_of_nonneg_left hx5 ht0]
    · nlinarith [mul_le_mul_of_nonneg_left hc6 ht0', mul_le_mul_of_nonneg_left hx6 ht0]

theorem w_abs : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i := by
  intro x hx i
  have hx1 : ((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s ≤ x 0 := hx.1.1
  have hx2 : x 0 ≤ ((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s := hx.1.2
  have hx3 : ((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s ≤ x 1 := hx.2.1.1
  have hx4 : x 1 ≤ ((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s := hx.2.1.2
  have hx5 : ((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s ≤ x 2 := hx.2.2.1
  have hx6 : x 2 ≤ ((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s := hx.2.2.2
  rw [s_eq] at hx1 hx2 hx3 hx4 hx5 hx6
  fin_cases i
  · change |x 0 - c0| ≤ w0
    rw [abs_le]; constructor
    · simp only [c0, w0]; linarith
    · simp only [c0, w0]; linarith
  · change |x 1 - c1| ≤ w1
    rw [abs_le]; constructor
    · simp only [c1, w1]; linarith
    · simp only [c1, w1]; linarith
  · change |x 2 - c2| ≤ w2
    rw [abs_le]; constructor
    · simp only [c2, w2]; linarith
    · simp only [c2, w2]; linarith

/-- `constDC` — a constant jet with a prescribed `DC` bracket (the `DC`
analogue of `constJet`; `DCJetKit.const` only covers integer constants). -/
def constDC (V : DC) (v : ℝ) : DCJet := ⟨V, fun _ => dInt 0⟩

theorem constDC_mem (V : DC) (v : ℝ) (h : V.mem v) (E : Set (Fin 3 → ℝ)) :
    JetMem (constDC V v) (fun _ : Fin 3 → ℝ => v) E := by
  refine ⟨fun _ _ => contDiffAt_const, fun _ _ => h, fun x _ i => ?_⟩
  have h0 : partial1 i (fun _ : Fin 3 → ℝ => v) x = 0 := by simp [partial1]
  rw [h0]
  simpa [constDC] using dInt_mem 0

/-- `√2` bracket, outward on `2^-60` (from the landed pilot). -/
def SIbr : DC := ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩

theorem SIbr_mem : SIbr.mem (Real.sqrt 2) := by
  refine ⟨?_, ?_⟩
  · show (((1630477228166597776 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(60 : ℤ)) ≤ Real.sqrt 2
    rw [Real.le_sqrt (by norm_num)] <;> norm_num
  · show Real.sqrt 2 ≤ (((1630477228166597777 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(60 : ℤ))
    rw [Real.sqrt_le_left (by norm_num)] <;> norm_num


/-- `MM1` bracket, outward on `2^-200` from `lk_mm1_mem`. -/
def MM1br : DC := ⟨(200 : ℤ), (1626351141384074285262729427986317719690753223710083998986084 : ℤ), (1626351302077878711161756982182526953807013475930383377265369 : ℤ)⟩

theorem MM1br_mem : MM1br.mem mm1 := by
  have h := lk_mm1_mem
  have h1 : (((1626351141384074285262729427986317719690753223710083998986084 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤ ((1.0120808 : ℚ) : ℝ) := by
    norm_num
  have h2 : ((1.0120809 : ℚ) : ℝ) ≤ (((1626351302077878711161756982182526953807013475930383377265369 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) := by
    norm_num
  exact ⟨le_trans h1 h.1, le_trans h.2 h2⟩


/-- `MM2` bracket, outward on `2^-200` from `lk_mm2_mem`. -/
def MM2br : DC := ⟨(200 : ℤ), (40839526925820108357761195595804476961800527985492788512766 : ℤ), (40839542995200550947663951015425400373426553207522726340696 : ℤ)⟩

theorem MM2br_mem : MM2br.mem mm2 := by
  have h := lk_mm2_mem
  have h1 : (((40839526925820108357761195595804476961800527985492788512766 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤ ((0.02541450 : ℚ) : ℝ) := by
    norm_num
  have h2 : ((0.02541451 : ℚ) : ℝ) ≤ (((40839542995200550947663951015425400373426553207522726340696 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) := by
    norm_num
  exact ⟨le_trans h1 h.1, le_trans h.2 h2⟩


/-! ## 1. The slot functions (mirror of `W1aFJet` §3, op-for-op) -/

def fY4 : (Fin 3 → ℝ) → ℝ := fun x => x 0
def fY5 : (Fin 3 → ℝ) → ℝ := fun x => x 1
def fY6 : (Fin 3 → ℝ) → ℝ := fun x => x 2
def fSI : (Fin 3 → ℝ) → ℝ := fun _ => Real.sqrt 2
def fPI : (Fin 3 → ℝ) → ℝ := fun _ => Real.pi
def fMM1 : (Fin 3 → ℝ) → ℝ := fun _ => mm1
def fMM2 : (Fin 3 → ℝ) → ℝ := fun _ => mm2
def fC2 : (Fin 3 → ℝ) → ℝ := fun x => ((2 : ℤ) : ℝ)
def fC4 : (Fin 3 → ℝ) → ℝ := fun x => ((4 : ℤ) : ℝ)
def fC8 : (Fin 3 → ℝ) → ℝ := fun x => ((8 : ℤ) : ℝ)
def fCN2 : (Fin 3 → ℝ) → ℝ := fun x => ((-2 : ℤ) : ℝ)
def fCH : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 2 : ℝ)
def fCH0 : (Fin 3 → ℝ) → ℝ := fun _ => (63 / 50 : ℝ)
def fCH0i : (Fin 3 → ℝ) → ℝ := fun _ => (50 / 13 : ℝ)
def fC008 : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 125 : ℝ)
def fC112 : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 12 : ℝ)
def fX4 : (Fin 3 → ℝ) → ℝ := fun x => fY4 x * fY4 x
def fX5 : (Fin 3 → ℝ) → ℝ := fun x => fY5 x * fY5 x
def fX6 : (Fin 3 → ℝ) → ℝ := fun x => fY6 x * fY6 x
def fX4sq : (Fin 3 → ℝ) → ℝ := fun x => fX4 x * fX4 x
def fX5sq : (Fin 3 → ℝ) → ℝ := fun x => fX5 x * fX5 x
def fX6sq : (Fin 3 → ℝ) → ℝ := fun x => fX6 x * fX6 x
def fS2a : (Fin 3 → ℝ) → ℝ := fun x => fX4sq x + fX5sq x
def fS2 : (Fin 3 → ℝ) → ℝ := fun x => fS2a x + fX6sq x
def fX4X5 : (Fin 3 → ℝ) → ℝ := fun x => fX4 x * fX5 x
def fX4X6 : (Fin 3 → ℝ) → ℝ := fun x => fX4 x * fX6 x
def fX5X6 : (Fin 3 → ℝ) → ℝ := fun x => fX5 x * fX6 x
def fS1a : (Fin 3 → ℝ) → ℝ := fun x => fX4X5 x + fX4X6 x
def fS1 : (Fin 3 → ℝ) → ℝ := fun x => fS1a x + fX5X6 x
def fCN2S2 : (Fin 3 → ℝ) → ℝ := fun x => fCN2 x * fS2 x
def fC4S1 : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fS1 x
def fDltA : (Fin 3 → ℝ) → ℝ := fun x => fCN2S2 x + fC4S1 x
def fX4X5X6 : (Fin 3 → ℝ) → ℝ := fun x => fX4X5 x * fX6 x
def fDlt : (Fin 3 → ℝ) → ℝ := fun x => fDltA x - fX4X5X6 x
def fSIY5 : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fY5 x
def fSIY5Y4 : (Fin 3 → ℝ) → ℝ := fun x => fSIY5 x * fY4 x
def fY5X4 : (Fin 3 → ℝ) → ℝ := fun x => fY5 x * fX4 x
def fY5X4CH : (Fin 3 → ℝ) → ℝ := fun x => fY5X4 x * fCH x
def fA1 : (Fin 3 → ℝ) → ℝ := fun x => fSIY5Y4 x + fY5X4CH x
def fX5X4 : (Fin 3 → ℝ) → ℝ := fun x => fX5 x + fX4 x
def fQA : (Fin 3 → ℝ) → ℝ := fun x => fX5X4 x - fX6 x
def fSIQA : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fQA x
def fSIQACH : (Fin 3 → ℝ) → ℝ := fun x => fSIQA x * fCH x
def fA2 : (Fin 3 → ℝ) → ℝ := fun x => fA1 x + fSIQACH x
def fY4X5 : (Fin 3 → ℝ) → ℝ := fun x => fY4 x * fX5 x
def fY4X5CH : (Fin 3 → ℝ) → ℝ := fun x => fY4X5 x * fCH x
def fA : (Fin 3 → ℝ) → ℝ := fun x => fA2 x + fY4X5CH x
def fSIY6 : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fY6 x
def fSIY6Y5 : (Fin 3 → ℝ) → ℝ := fun x => fSIY6 x * fY5 x
def fY6X5 : (Fin 3 → ℝ) → ℝ := fun x => fY6 x * fX5 x
def fY6X5CH : (Fin 3 → ℝ) → ℝ := fun x => fY6X5 x * fCH x
def fB1 : (Fin 3 → ℝ) → ℝ := fun x => fSIY6Y5 x + fY6X5CH x
def fX6X5 : (Fin 3 → ℝ) → ℝ := fun x => fX6 x + fX5 x
def fQB : (Fin 3 → ℝ) → ℝ := fun x => fX6X5 x - fX4 x
def fSIQB : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fQB x
def fSIQBCH : (Fin 3 → ℝ) → ℝ := fun x => fSIQB x * fCH x
def fB2 : (Fin 3 → ℝ) → ℝ := fun x => fB1 x + fSIQBCH x
def fY5X6 : (Fin 3 → ℝ) → ℝ := fun x => fY5 x * fX6 x
def fY5X6CH : (Fin 3 → ℝ) → ℝ := fun x => fY5X6 x * fCH x
def fB : (Fin 3 → ℝ) → ℝ := fun x => fB2 x + fY5X6CH x
def fSIY4 : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fY4 x
def fSIY4Y6 : (Fin 3 → ℝ) → ℝ := fun x => fSIY4 x * fY6 x
def fY4X6 : (Fin 3 → ℝ) → ℝ := fun x => fY4 x * fX6 x
def fY4X6CH : (Fin 3 → ℝ) → ℝ := fun x => fY4X6 x * fCH x
def fC1 : (Fin 3 → ℝ) → ℝ := fun x => fSIY4Y6 x + fY4X6CH x
def fX4X6add : (Fin 3 → ℝ) → ℝ := fun x => fX4 x + fX6 x
def fQC : (Fin 3 → ℝ) → ℝ := fun x => fX4X6add x - fX5 x
def fSIQC : (Fin 3 → ℝ) → ℝ := fun x => fSI x * fQC x
def fSIQCCH : (Fin 3 → ℝ) → ℝ := fun x => fSIQC x * fCH x
def fC2b : (Fin 3 → ℝ) → ℝ := fun x => fC1 x + fSIQCCH x
def fY6X4 : (Fin 3 → ℝ) → ℝ := fun x => fY6 x * fX4 x
def fY6X4CH : (Fin 3 → ℝ) → ℝ := fun x => fY6X4 x * fCH x
def fC : (Fin 3 → ℝ) → ℝ := fun x => fC2b x + fY6X4CH x
def fD4A : (Fin 3 → ℝ) → ℝ := fun x => fX5 x * fQC x
def fD4B : (Fin 3 → ℝ) → ℝ := fun x => fX6 x * fQA x
def fD4C : (Fin 3 → ℝ) → ℝ := fun x => fX4 x * fQB x
def fKA : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fX5 x
def fKB : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fX6 x
def fKC : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fX4 x
def fNA : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY5 x
def fNB : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY6 x
def fNC : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY4 x
def fY4CH : (Fin 3 → ℝ) → ℝ := fun x => fY4 x * fCH x
def fY5CH : (Fin 3 → ℝ) → ℝ := fun x => fY5 x * fCH x
def fY6CH : (Fin 3 → ℝ) → ℝ := fun x => fY6 x * fCH x
def fCH0m4 : (Fin 3 → ℝ) → ℝ := fun x => fCH0 x - fY4CH x
def fCH0m5 : (Fin 3 → ℝ) → ℝ := fun x => fCH0 x - fY5CH x
def fCH0m6 : (Fin 3 → ℝ) → ℝ := fun x => fCH0 x - fY6CH x
def fLf4 : (Fin 3 → ℝ) → ℝ := fun x => fCH0m4 x * fCH0i x
def fLf5 : (Fin 3 → ℝ) → ℝ := fun x => fCH0m5 x * fCH0i x
def fLf6 : (Fin 3 → ℝ) → ℝ := fun x => fCH0m6 x * fCH0i x
def fINVPI : (Fin 3 → ℝ) → ℝ := fun x => (fPI x)⁻¹
def fC2MM1 : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fMM1 x
def fK1 : (Fin 3 → ℝ) → ℝ := fun x => fC2MM1 x * fINVPI x
def fC8MM2 : (Fin 3 → ℝ) → ℝ := fun x => fC8 x * fMM2 x
def fK2 : (Fin 3 → ℝ) → ℝ := fun x => fC8MM2 x * fINVPI x
def fAsq : (Fin 3 → ℝ) → ℝ := fun x => fA x * fA x
def fF4A : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fAsq x
def fBsq : (Fin 3 → ℝ) → ℝ := fun x => fB x * fB x
def fF4B : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fBsq x
def fCsq : (Fin 3 → ℝ) → ℝ := fun x => fC x * fC x
def fF4C : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * fCsq x
def fD4Asq : (Fin 3 → ℝ) → ℝ := fun x => fD4A x * fD4A x
def fD4Bsq : (Fin 3 → ℝ) → ℝ := fun x => fD4B x * fD4B x
def fD4Csq : (Fin 3 → ℝ) → ℝ := fun x => fD4C x * fD4C x
def fT4A : (Fin 3 → ℝ) → ℝ := fun x => (fF4A x)⁻¹
def fT4B : (Fin 3 → ℝ) → ℝ := fun x => (fF4B x)⁻¹
def fT4C : (Fin 3 → ℝ) → ℝ := fun x => (fF4C x)⁻¹
def fTA : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4A x
def fTB : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4B x
def fTC : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4C x
def fInvA2A : (Fin 3 → ℝ) → ℝ := fun x => (fD4Asq x)⁻¹
def fInvA2B : (Fin 3 → ℝ) → ℝ := fun x => (fD4Bsq x)⁻¹
def fInvA2C : (Fin 3 → ℝ) → ℝ := fun x => (fD4Csq x)⁻¹
def fKDltA : (Fin 3 → ℝ) → ℝ := fun x => fKA x * fDlt x
def fKDltB : (Fin 3 → ℝ) → ℝ := fun x => fKB x * fDlt x
def fKDltC : (Fin 3 → ℝ) → ℝ := fun x => fKC x * fDlt x
def fGA : (Fin 3 → ℝ) → ℝ := fun x => fKDltA x * fInvA2A x
def fGB : (Fin 3 → ℝ) → ℝ := fun x => fKDltB x * fInvA2B x
def fGC : (Fin 3 → ℝ) → ℝ := fun x => fKDltC x * fInvA2C x
def fInvD4A : (Fin 3 → ℝ) → ℝ := fun x => (fD4A x)⁻¹
def fInvD4B : (Fin 3 → ℝ) → ℝ := fun x => (fD4B x)⁻¹
def fInvD4C : (Fin 3 → ℝ) → ℝ := fun x => (fD4C x)⁻¹
def fIA : (Fin 3 → ℝ) → ℝ := fun x => (fA x)⁻¹
def fIB : (Fin 3 → ℝ) → ℝ := fun x => (fB x)⁻¹
def fIC : (Fin 3 → ℝ) → ℝ := fun x => (fC x)⁻¹
def fWA : (Fin 3 → ℝ) → ℝ := fun x => fNA x * fInvD4A x
def fWB : (Fin 3 → ℝ) → ℝ := fun x => fNB x * fInvD4B x
def fWC : (Fin 3 → ℝ) → ℝ := fun x => fNC x * fInvD4C x
def fMtA : (Fin 3 → ℝ) → ℝ := fun x => matan (fTA x)
def fMtB : (Fin 3 → ℝ) → ℝ := fun x => matan (fTB x)
def fMtC : (Fin 3 → ℝ) → ℝ := fun x => matan (fTC x)
def fMgA : (Fin 3 → ℝ) → ℝ := fun x => matan (fGA x)
def fMgB : (Fin 3 → ℝ) → ℝ := fun x => matan (fGB x)
def fMgC : (Fin 3 → ℝ) → ℝ := fun x => matan (fGC x)
def fDihA : (Fin 3 → ℝ) → ℝ := fun x => fWA x * fMgA x
def fDihB : (Fin 3 → ℝ) → ℝ := fun x => fWB x * fMgB x
def fDihC : (Fin 3 → ℝ) → ℝ := fun x => fWC x * fMgC x
def fSeA : (Fin 3 → ℝ) → ℝ := fun x => fMtA x * fIA x
def fSeB : (Fin 3 → ℝ) → ℝ := fun x => fMtB x * fIB x
def fSeC : (Fin 3 → ℝ) → ℝ := fun x => fMtC x * fIC x
def fSe1 : (Fin 3 → ℝ) → ℝ := fun x => fSeA x + fSeB x
def fSe : (Fin 3 → ℝ) → ℝ := fun x => fSe1 x + fSeC x
def fK1Se : (Fin 3 → ℝ) → ℝ := fun x => fK1 x * fSe x
def fFirst : (Fin 3 → ℝ) → ℝ := fun x => fC112 x - fK1Se x
def fLf5DihA : (Fin 3 → ℝ) → ℝ := fun x => fLf5 x * fDihA x
def fLf6DihB : (Fin 3 → ℝ) → ℝ := fun x => fLf6 x * fDihB x
def fPosA : (Fin 3 → ℝ) → ℝ := fun x => fLf5DihA x + fLf6DihB x
def fPos : (Fin 3 → ℝ) → ℝ := fun x => fK2 x * fPosA x
def fNeg2 : (Fin 3 → ℝ) → ℝ := fun x => fC008 x * fDihC x
def fFirstPos : (Fin 3 → ℝ) → ℝ := fun x => fFirst x + fPos x
def fTop : (Fin 3 → ℝ) → ℝ := fun x => fFirstPos x - fNeg2 x


/-! ## 2. The shared constant jets (box- and point-independent) -/

def JSI : DCJet := constDC SIbr (Real.sqrt 2)
theorem JSI_mem (E : Set (Fin 3 → ℝ)) : JetMem JSI fSI E :=
  constDC_mem SIbr _ SIbr_mem E

theorem ev_SI : (JSI).value = ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ := by rfl

theorem p0_SI : (JSI).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_SI : (JSI).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_SI : (JSI).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JPI : DCJet := constDC PIbr (Real.pi)
theorem JPI_mem (E : Set (Fin 3 → ℝ)) : JetMem JPI fPI E :=
  constDC_mem PIbr _ PIbr_mem E

theorem ev_PI : (JPI).value = ⟨(40 : ℤ), (3454217652357 : ℤ), (3454217652358 : ℤ)⟩ := by rfl

theorem p0_PI : (JPI).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_PI : (JPI).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_PI : (JPI).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JMM1 : DCJet := constDC MM1br (mm1)
theorem JMM1_mem (E : Set (Fin 3 → ℝ)) : JetMem JMM1 fMM1 E :=
  constDC_mem MM1br _ MM1br_mem E

theorem ev_MM1 : (JMM1).value = ⟨(200 : ℤ), (1626351141384074285262729427986317719690753223710083998986084 : ℤ), (1626351302077878711161756982182526953807013475930383377265369 : ℤ)⟩ := by rfl

theorem p0_MM1 : (JMM1).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_MM1 : (JMM1).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_MM1 : (JMM1).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JMM2 : DCJet := constDC MM2br (mm2)
theorem JMM2_mem (E : Set (Fin 3 → ℝ)) : JetMem JMM2 fMM2 E :=
  constDC_mem MM2br _ MM2br_mem E

theorem ev_MM2 : (JMM2).value = ⟨(200 : ℤ), (40839526925820108357761195595804476961800527985492788512766 : ℤ), (40839542995200550947663951015425400373426553207522726340696 : ℤ)⟩ := by rfl

theorem p0_MM2 : (JMM2).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_MM2 : (JMM2).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_MM2 : (JMM2).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JC2 : DCJet := DCJetKit.const (2 : ℤ)
theorem JC2_mem (E : Set (Fin 3 → ℝ)) : JetMem JC2 fC2 E :=
  DCJetKit.const_mem (2 : ℤ) E

theorem ev_C2 : (JC2).value = ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ := by rfl

theorem p0_C2 : (JC2).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_C2 : (JC2).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_C2 : (JC2).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JC4 : DCJet := DCJetKit.const (4 : ℤ)
theorem JC4_mem (E : Set (Fin 3 → ℝ)) : JetMem JC4 fC4 E :=
  DCJetKit.const_mem (4 : ℤ) E

theorem ev_C4 : (JC4).value = ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ := by rfl

theorem p0_C4 : (JC4).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_C4 : (JC4).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_C4 : (JC4).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JC8 : DCJet := DCJetKit.const (8 : ℤ)
theorem JC8_mem (E : Set (Fin 3 → ℝ)) : JetMem JC8 fC8 E :=
  DCJetKit.const_mem (8 : ℤ) E

theorem ev_C8 : (JC8).value = ⟨(0 : ℤ), (8 : ℤ), (8 : ℤ)⟩ := by rfl

theorem p0_C8 : (JC8).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_C8 : (JC8).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_C8 : (JC8).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JCN2 : DCJet := DCJetKit.const (-2 : ℤ)
theorem JCN2_mem (E : Set (Fin 3 → ℝ)) : JetMem JCN2 fCN2 E :=
  DCJetKit.const_mem (-2 : ℤ) E

theorem ev_CN2 : (JCN2).value = ⟨(0 : ℤ), (-2 : ℤ), (-2 : ℤ)⟩ := by rfl

theorem p0_CN2 : (JCN2).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_CN2 : (JCN2).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_CN2 : (JCN2).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JCH : DCJet := constDC (dDiv (dInt 1) (dInt 2)) (1 / 2 : ℝ)
theorem JCH_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH fCH E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 2)) E

theorem ev_CH : (JCH).value = ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by rfl

theorem p0_CH : (JCH).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_CH : (JCH).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_CH : (JCH).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JCH0 : DCJet := constDC (dDiv (dInt 63) (dInt 50)) (63 / 50 : ℝ)
theorem JCH0_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH0 fCH0 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 63) (dInt_mem 50)) E

theorem ev_CH0 : (JCH0).value = ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ := by rfl

theorem p0_CH0 : (JCH0).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_CH0 : (JCH0).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_CH0 : (JCH0).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JCH0i : DCJet := constDC (dDiv (dInt 50) (dInt 13)) (50 / 13 : ℝ)
theorem JCH0i_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH0i fCH0i E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 50) (dInt_mem 13)) E

theorem ev_CH0i : (JCH0i).value = ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ := by rfl

theorem p0_CH0i : (JCH0i).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_CH0i : (JCH0i).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_CH0i : (JCH0i).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JC008 : DCJet := constDC (dDiv (dInt 1) (dInt 125)) (1 / 125 : ℝ)
theorem JC008_mem (E : Set (Fin 3 → ℝ)) : JetMem JC008 fC008 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 125)) E

theorem ev_C008 : (JC008).value = ⟨(206 : ℤ), (822752278660603021077484591278675252491367932816789931674304 : ℤ), (822752278660603021077484591278675252491367932816789931674305 : ℤ)⟩ := by rfl

theorem p0_C008 : (JC008).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_C008 : (JC008).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_C008 : (JC008).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

def JC112 : DCJet := constDC (dDiv (dInt 1) (dInt 12)) (1 / 12 : ℝ)
theorem JC112_mem (E : Set (Fin 3 → ℝ)) : JetMem JC112 fC112 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 12)) E

theorem ev_C112 : (JC112).value = ⟨(203 : ℤ), (1071292029505993517027974728227441735014801995855195223534250 : ℤ), (1071292029505993517027974728227441735014801995855195223534251 : ℤ)⟩ := by rfl

theorem p0_C112 : (JC112).part 0 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p1_C112 : (JC112).part 1 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl

theorem p2_C112 : (JC112).part 2 = ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by rfl


/-! ## 3. Box pass -/

namespace Box

def JY4 : DCJet := DCJetKit.coord 0 I4
theorem JY4_mem : JetMem JY4 fY4 D :=
  DCJetKit.coord_mem 0 I4 D (fun x hx => hx.1)

theorem ev_Y4 : (JY4).value = ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ := by rfl

theorem p0_Y4 : (JY4).part 0 = dInt 1 := by
  show dInt (if (0 : Fin 3) = 0 then (1 : ℤ) else 0) = dInt 1
  rw [if_pos (by decide)]

theorem p1_Y4 : (JY4).part 1 = dInt 0 := by
  show dInt (if (1 : Fin 3) = 0 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

theorem p2_Y4 : (JY4).part 2 = dInt 0 := by
  show dInt (if (2 : Fin 3) = 0 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

def JY5 : DCJet := DCJetKit.coord 1 I5
theorem JY5_mem : JetMem JY5 fY5 D :=
  DCJetKit.coord_mem 1 I5 D (fun x hx => hx.2.1)

theorem ev_Y5 : (JY5).value = ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ := by rfl

theorem p0_Y5 : (JY5).part 0 = dInt 0 := by
  show dInt (if (0 : Fin 3) = 1 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

theorem p1_Y5 : (JY5).part 1 = dInt 1 := by
  show dInt (if (1 : Fin 3) = 1 then (1 : ℤ) else 0) = dInt 1
  rw [if_pos (by decide)]

theorem p2_Y5 : (JY5).part 2 = dInt 0 := by
  show dInt (if (2 : Fin 3) = 1 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

def JY6 : DCJet := DCJetKit.coord 2 I6
theorem JY6_mem : JetMem JY6 fY6 D :=
  DCJetKit.coord_mem 2 I6 D (fun x hx => hx.2.2)

theorem ev_Y6 : (JY6).value = ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ := by rfl

theorem p0_Y6 : (JY6).part 0 = dInt 0 := by
  show dInt (if (0 : Fin 3) = 2 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

theorem p1_Y6 : (JY6).part 1 = dInt 0 := by
  show dInt (if (1 : Fin 3) = 2 then (1 : ℤ) else 0) = dInt 0
  rw [if_neg (by decide)]

theorem p2_Y6 : (JY6).part 2 = dInt 1 := by
  show dInt (if (2 : Fin 3) = 2 then (1 : ℤ) else 0) = dInt 1
  rw [if_pos (by decide)]

def JX4 : DCJet := DCJetKit.mul JY4 JY4
theorem JX4_mem : JetMem JX4 fX4 D :=
  DCJetKit.mul_mem (JY4_mem) (JY4_mem)

theorem op_X4 : dMul ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ = ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rfl

theorem ev_X4 : (JX4).value = ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JX4).value = dMul (JY4).value (JY4).value from rfl, ev_Y4]
  exact op_X4

theorem p0_X4 : (JX4).part 0 = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JX4).part 0 = dAdd (dMul (JY4).value ((JY4).part 0)) (dMul (JY4).value ((JY4).part 0)) from rfl, ev_Y4, p0_Y4]
  rfl

theorem p1_X4 : (JX4).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4).part 1 = dAdd (dMul (JY4).value ((JY4).part 1)) (dMul (JY4).value ((JY4).part 1)) from rfl, ev_Y4, p1_Y4]
  rfl

theorem p2_X4 : (JX4).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4).part 2 = dAdd (dMul (JY4).value ((JY4).part 2)) (dMul (JY4).value ((JY4).part 2)) from rfl, ev_Y4, p2_Y4]
  rfl

def JX5 : DCJet := DCJetKit.mul JY5 JY5
theorem JX5_mem : JetMem JX5 fX5 D :=
  DCJetKit.mul_mem (JY5_mem) (JY5_mem)

theorem op_X5 : dMul ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ = ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rfl

theorem ev_X5 : (JX5).value = ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JX5).value = dMul (JY5).value (JY5).value from rfl, ev_Y5]
  exact op_X5

theorem p0_X5 : (JX5).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5).part 0 = dAdd (dMul (JY5).value ((JY5).part 0)) (dMul (JY5).value ((JY5).part 0)) from rfl, ev_Y5, p0_Y5]
  rfl

theorem p1_X5 : (JX5).part 1 = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JX5).part 1 = dAdd (dMul (JY5).value ((JY5).part 1)) (dMul (JY5).value ((JY5).part 1)) from rfl, ev_Y5, p1_Y5]
  rfl

theorem p2_X5 : (JX5).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5).part 2 = dAdd (dMul (JY5).value ((JY5).part 2)) (dMul (JY5).value ((JY5).part 2)) from rfl, ev_Y5, p2_Y5]
  rfl

def JX6 : DCJet := DCJetKit.mul JY6 JY6
theorem JX6_mem : JetMem JX6 fX6 D :=
  DCJetKit.mul_mem (JY6_mem) (JY6_mem)

theorem op_X6 : dMul ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ = ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rfl

theorem ev_X6 : (JX6).value = ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JX6).value = dMul (JY6).value (JY6).value from rfl, ev_Y6]
  exact op_X6

theorem p0_X6 : (JX6).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX6).part 0 = dAdd (dMul (JY6).value ((JY6).part 0)) (dMul (JY6).value ((JY6).part 0)) from rfl, ev_Y6, p0_Y6]
  rfl

theorem p1_X6 : (JX6).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX6).part 1 = dAdd (dMul (JY6).value ((JY6).part 1)) (dMul (JY6).value ((JY6).part 1)) from rfl, ev_Y6, p1_Y6]
  rfl

theorem p2_X6 : (JX6).part 2 = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JX6).part 2 = dAdd (dMul (JY6).value ((JY6).part 2)) (dMul (JY6).value ((JY6).part 2)) from rfl, ev_Y6, p2_Y6]
  rfl

def JX4sq : DCJet := DCJetKit.mul JX4 JX4
theorem JX4sq_mem : JetMem JX4sq fX4sq D :=
  DCJetKit.mul_mem (JX4_mem) (JX4_mem)

theorem op_X4sq : dMul ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ = ⟨(194 : ℤ), (1012561293625125908399671308165149326887630615805743120223277 : ℤ), (1012561293626122461581416633215636923180739120414425767361397 : ℤ)⟩ := by
  rfl

theorem ev_X4sq : (JX4sq).value = ⟨(194 : ℤ), (1012561293625125908399671308165149326887630615805743120223277 : ℤ), (1012561293626122461581416633215636923180739120414425767361397 : ℤ)⟩ := by
  rw [show (JX4sq).value = dMul (JX4).value (JX4).value from rfl, ev_X4]
  exact op_X4sq

theorem p0_X4sq : (JX4sq).part 0 = ⟨(193 : ℤ), (803620074305655482856881990607261370545738583972812000177204 : ℤ), (803620074306248669274587468256498742518912889424023852370967 : ℤ)⟩ := by
  rw [show (JX4sq).part 0 = dAdd (dMul (JX4).value ((JX4).part 0)) (dMul (JX4).value ((JX4).part 0)) from rfl, ev_X4, p0_X4]
  rfl

theorem p1_X4sq : (JX4sq).part 1 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4sq).part 1 = dAdd (dMul (JX4).value ((JX4).part 1)) (dMul (JX4).value ((JX4).part 1)) from rfl, ev_X4, p1_X4]
  rfl

theorem p2_X4sq : (JX4sq).part 2 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4sq).part 2 = dAdd (dMul (JX4).value ((JX4).part 2)) (dMul (JX4).value ((JX4).part 2)) from rfl, ev_X4, p2_X4]
  rfl

def JX5sq : DCJet := DCJetKit.mul JX5 JX5
theorem JX5sq_mem : JetMem JX5sq fX5sq D :=
  DCJetKit.mul_mem (JX5_mem) (JX5_mem)

theorem op_X5sq : dMul ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(195 : ℤ), (1347213707118160036381933685483931547094791027802219285589197 : ℤ), (1465350818223167051558556956512010742635643838333694006980802 : ℤ)⟩ := by
  rfl

theorem ev_X5sq : (JX5sq).value = ⟨(195 : ℤ), (1347213707118160036381933685483931547094791027802219285589197 : ℤ), (1465350818223167051558556956512010742635643838333694006980802 : ℤ)⟩ := by
  rw [show (JX5sq).value = dMul (JX5).value (JX5).value from rfl, ev_X5]
  exact op_X5sq

theorem p0_X5sq : (JX5sq).part 0 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5sq).part 0 = dAdd (dMul (JX5).value ((JX5).part 0)) (dMul (JX5).value ((JX5).part 0)) from rfl, ev_X5, p0_X5]
  rfl

theorem p1_X5sq : (JX5sq).part 1 = ⟨(194 : ℤ), (1183912630793926101121210235008664552626970420449296463240887 : ℤ), (1260951819482331590446277711936573835542758467346198814066447 : ℤ)⟩ := by
  rw [show (JX5sq).part 1 = dAdd (dMul (JX5).value ((JX5).part 1)) (dMul (JX5).value ((JX5).part 1)) from rfl, ev_X5, p1_X5]
  rfl

theorem p2_X5sq : (JX5sq).part 2 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5sq).part 2 = dAdd (dMul (JX5).value ((JX5).part 2)) (dMul (JX5).value ((JX5).part 2)) from rfl, ev_X5, p2_X5]
  rfl

def JX6sq : DCJet := DCJetKit.mul JX6 JX6
theorem JX6sq_mem : JetMem JX6sq fX6sq D :=
  DCJetKit.mul_mem (JX6_mem) (JX6_mem)

theorem op_X6sq : dMul ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(195 : ℤ), (1406891867869794309711491069350774345732060522799761018872513 : ℤ), (1547727097271952523852397136937631034218164988822564182251546 : ℤ)⟩ := by
  rfl

theorem ev_X6sq : (JX6sq).value = ⟨(195 : ℤ), (1406891867869794309711491069350774345732060522799761018872513 : ℤ), (1547727097271952523852397136937631034218164988822564182251546 : ℤ)⟩ := by
  rw [show (JX6sq).value = dMul (JX6).value (JX6).value from rfl, ev_X6]
  exact op_X6sq

theorem p0_X6sq : (JX6sq).part 0 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX6sq).part 0 = dAdd (dMul (JX6).value ((JX6).part 0)) (dMul (JX6).value ((JX6).part 0)) from rfl, ev_X6, p0_X6]
  rfl

theorem p1_X6sq : (JX6sq).part 1 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX6sq).part 1 = dAdd (dMul (JX6).value ((JX6).part 1)) (dMul (JX6).value ((JX6).part 1)) from rfl, ev_X6, p1_X6]
  rfl

theorem p2_X6sq : (JX6sq).part 2 = ⟨(194 : ℤ), (1223032009872520673839499211475121560678085775352331361294972 : ℤ), (1313751043305869213046764753546432444449075019647790757471160 : ℤ)⟩ := by
  rw [show (JX6sq).part 2 = dAdd (dMul (JX6).value ((JX6).part 2)) (dMul (JX6).value ((JX6).part 2)) from rfl, ev_X6, p2_X6]
  rfl

def JS2a : DCJet := DCJetKit.add JX4sq JX5sq
theorem JS2a_mem : JetMem JS2a fS2a D :=
  DCJetKit.add_mem (JX4sq_mem) (JX5sq_mem)

theorem op_S2a : dAdd ⟨(194 : ℤ), (1012561293625125908399671308165149326887630615805743120223277 : ℤ), (1012561293626122461581416633215636923180739120414425767361397 : ℤ)⟩ ⟨(195 : ℤ), (1347213707118160036381933685483931547094791027802219285589197 : ℤ), (1465350818223167051558556956512010742635643838333694006980802 : ℤ)⟩ = ⟨(193 : ℤ), (843084073592102963295319075453557550217513064853426381508937 : ℤ), (872618351368852993680347555735821147249280519790636385425899 : ℤ)⟩ := by
  rfl

theorem ev_S2a : (JS2a).value = ⟨(193 : ℤ), (843084073592102963295319075453557550217513064853426381508937 : ℤ), (872618351368852993680347555735821147249280519790636385425899 : ℤ)⟩ := by
  rw [show (JS2a).value = dAdd (JX4sq).value (JX5sq).value from rfl, ev_X4sq, ev_X5sq]
  exact op_S2a

theorem p0_S2a : (JS2a).part 0 = ⟨(193 : ℤ), (803620074305655482856881990607261370545738583972812000177204 : ℤ), (803620074306248669274587468256498742518912889424023852370967 : ℤ)⟩ := by
  rw [show (JS2a).part 0 = dAdd ((JX4sq).part 0) ((JX5sq).part 0) from rfl, p0_X4sq, p0_X5sq]
  rfl

theorem p1_S2a : (JS2a).part 1 = ⟨(194 : ℤ), (1183912630793926101121210235008664552626970420449296463240887 : ℤ), (1260951819482331590446277711936573835542758467346198814066447 : ℤ)⟩ := by
  rw [show (JS2a).part 1 = dAdd ((JX4sq).part 1) ((JX5sq).part 1) from rfl, p1_X4sq, p1_X5sq]
  rfl

theorem p2_S2a : (JS2a).part 2 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JS2a).part 2 = dAdd ((JX4sq).part 2) ((JX5sq).part 2) from rfl, p2_X4sq, p2_X5sq]
  rfl

def JS2 : DCJet := DCJetKit.add JS2a JX6sq
theorem JS2_mem : JetMem JS2 fS2 D :=
  DCJetKit.add_mem (JS2a_mem) (JX6sq_mem)

theorem op_S2 : dAdd ⟨(193 : ℤ), (843084073592102963295319075453557550217513064853426381508937 : ℤ), (872618351368852993680347555735821147249280519790636385425899 : ℤ)⟩ ⟨(195 : ℤ), (1406891867869794309711491069350774345732060522799761018872513 : ℤ), (1547727097271952523852397136937631034218164988822564182251546 : ℤ)⟩ = ⟨(193 : ℤ), (1194807040559551540723191842791251136650528195553366636227065 : ℤ), (1259550125686841124643446839970228905803821766996277430988786 : ℤ)⟩ := by
  rfl

theorem ev_S2 : (JS2).value = ⟨(193 : ℤ), (1194807040559551540723191842791251136650528195553366636227065 : ℤ), (1259550125686841124643446839970228905803821766996277430988786 : ℤ)⟩ := by
  rw [show (JS2).value = dAdd (JS2a).value (JX6sq).value from rfl, ev_S2a, ev_X6sq]
  exact op_S2

theorem p0_S2 : (JS2).part 0 = ⟨(193 : ℤ), (803620074305655482856881990607261370545738583972812000177204 : ℤ), (803620074306248669274587468256498742518912889424023852370967 : ℤ)⟩ := by
  rw [show (JS2).part 0 = dAdd ((JS2a).part 0) ((JX6sq).part 0) from rfl, p0_S2a, p0_X6sq]
  rfl

theorem p1_S2 : (JS2).part 1 = ⟨(194 : ℤ), (1183912630793926101121210235008664552626970420449296463240887 : ℤ), (1260951819482331590446277711936573835542758467346198814066447 : ℤ)⟩ := by
  rw [show (JS2).part 1 = dAdd ((JS2a).part 1) ((JX6sq).part 1) from rfl, p1_S2a, p1_X6sq]
  rfl

theorem p2_S2 : (JS2).part 2 = ⟨(194 : ℤ), (1223032009872520673839499211475121560678085775352331361294972 : ℤ), (1313751043305869213046764753546432444449075019647790757471160 : ℤ)⟩ := by
  rw [show (JS2).part 2 = dAdd ((JS2a).part 2) ((JX6sq).part 2) from rfl, p2_S2a, p2_X6sq]
  rfl

def JX4X5 : DCJet := DCJetKit.mul JX4 JX5
theorem JX4X5_mem : JetMem JX4X5 fX4X5 D :=
  DCJetKit.mul_mem (JX4_mem) (JX5_mem)

theorem op_X4X5 : dMul ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(194 : ℤ), (825874219863129527960407603870867911761373774876214810262600 : ℤ), (861323841570679806312249620866416671588236940392648069160396 : ℤ)⟩ := by
  rfl

theorem ev_X4X5 : (JX4X5).value = ⟨(194 : ℤ), (825874219863129527960407603870867911761373774876214810262600 : ℤ), (861323841570679806312249620866416671588236940392648069160396 : ℤ)⟩ := by
  rw [show (JX4X5).value = dMul (JX4).value (JX5).value from rfl, ev_X4, ev_X5]
  exact op_X4X5

theorem p0_X4X5 : (JX4X5).part 0 = ⟨(195 : ℤ), (1310911460100205599937154926779155415494244087105102873432699 : ℤ), (1367180700905504570844130569210936703029688179514780059040777 : ℤ)⟩ := by
  rw [show (JX4X5).part 0 = dAdd (dMul (JX4).value ((JX5).part 0)) (dMul (JX5).value ((JX4).part 0)) from rfl, ev_X4, ev_X5, p0_X4, p0_X5]
  rfl

theorem p1_X4X5 : (JX4X5).part 1 = ⟨(195 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rw [show (JX4X5).part 1 = dAdd (dMul (JX4).value ((JX5).part 1)) (dMul (JX5).value ((JX4).part 1)) from rfl, ev_X4, ev_X5, p1_X4, p1_X5]
  rfl

theorem p2_X4X5 : (JX4X5).part 2 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4X5).part 2 = dAdd (dMul (JX4).value ((JX5).part 2)) (dMul (JX5).value ((JX4).part 2)) from rfl, ev_X4, ev_X5, p2_X4, p2_X5]
  rfl

def JX4X6 : DCJet := DCJetKit.mul JX4 JX6
theorem JX4X6_mem : JetMem JX4X6 fX4X6 D :=
  DCJetKit.mul_mem (JX4_mem) (JX6_mem)

theorem op_X4X6 : dMul ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(194 : ℤ), (843968082844638337099132594938186603933444692386892886605221 : ℤ), (885202957460573478902905513489972663744338912879838914657122 : ℤ)⟩ := by
  rfl

theorem ev_X4X6 : (JX4X6).value = ⟨(194 : ℤ), (843968082844638337099132594938186603933444692386892886605221 : ℤ), (885202957460573478902905513489972663744338912879838914657122 : ℤ)⟩ := by
  rw [show (JX4X6).value = dMul (JX4).value (JX6).value from rfl, ev_X4, ev_X6]
  exact op_X4X6

theorem p0_X4X6 : (JX4X6).part 0 = ⟨(195 : ℤ), (1339631877531171963649416817362200958624515384741099820008288 : ℤ), (1405084059460882026702934098677799114174131535300239337345769 : ℤ)⟩ := by
  rw [show (JX4X6).part 0 = dAdd (dMul (JX4).value ((JX6).part 0)) (dMul (JX6).value ((JX4).part 0)) from rfl, ev_X4, ev_X6, p0_X4, p0_X6]
  rfl

theorem p1_X4X6 : (JX4X6).part 1 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4X6).part 1 = dAdd (dMul (JX4).value ((JX6).part 1)) (dMul (JX6).value ((JX4).part 1)) from rfl, ev_X4, ev_X6, p1_X4, p1_X6]
  rfl

theorem p2_X4X6 : (JX4X6).part 2 = ⟨(195 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391381 : ℤ)⟩ := by
  rw [show (JX4X6).part 2 = dAdd (dMul (JX4).value ((JX6).part 2)) (dMul (JX6).value ((JX4).part 2)) from rfl, ev_X4, ev_X6, p2_X4, p2_X6]
  rfl

def JX5X6 : DCJet := DCJetKit.mul JX5 JX6
theorem JX5X6_mem : JetMem JX5X6 fX5X6 D :=
  DCJetKit.mul_mem (JX5_mem) (JX6_mem)

theorem op_X5X6 : dMul ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(195 : ℤ), (1376729461015220005016887581010995972280086956417868416471207 : ℤ), (1505975819319029734400390200144498260173956375031885250841254 : ℤ)⟩ := by
  rfl

theorem ev_X5X6 : (JX5X6).value = ⟨(195 : ℤ), (1376729461015220005016887581010995972280086956417868416471207 : ℤ), (1505975819319029734400390200144498260173956375031885250841254 : ℤ)⟩ := by
  rw [show (JX5X6).value = dMul (JX5).value (JX6).value from rfl, ev_X5, ev_X6]
  exact op_X5X6

theorem p0_X5X6 : (JX5X6).part 0 = ⟨(397 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5X6).part 0 = dAdd (dMul (JX5).value ((JX6).part 0)) (dMul (JX6).value ((JX5).part 0)) from rfl, ev_X5, ev_X6, p0_X5, p0_X6]
  rfl

theorem p1_X5X6 : (JX5X6).part 1 = ⟨(195 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rw [show (JX5X6).part 1 = dAdd (dMul (JX5).value ((JX6).part 1)) (dMul (JX6).value ((JX5).part 1)) from rfl, ev_X5, ev_X6, p1_X5, p1_X6]
  rfl

theorem p2_X5X6 : (JX5X6).part 2 = ⟨(195 : ℤ), (1196811381322155933722889081010975019980752537494381738826067 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rw [show (JX5X6).part 2 = dAdd (dMul (JX5).value ((JX6).part 2)) (dMul (JX6).value ((JX5).part 2)) from rfl, ev_X5, ev_X6, p2_X5, p2_X6]
  rfl

def JS1a : DCJet := DCJetKit.add JX4X5 JX4X6
theorem JS1a_mem : JetMem JS1a fS1a D :=
  DCJetKit.add_mem (JX4X5_mem) (JX4X6_mem)

theorem op_S1a : dAdd ⟨(194 : ℤ), (825874219863129527960407603870867911761373774876214810262600 : ℤ), (861323841570679806312249620866416671588236940392648069160396 : ℤ)⟩ ⟨(194 : ℤ), (843968082844638337099132594938186603933444692386892886605221 : ℤ), (885202957460573478902905513489972663744338912879838914657122 : ℤ)⟩ = ⟨(193 : ℤ), (834921151353883932529770099404527257847409233631553848433910 : ℤ), (873263399515626642607577567178194667666287926636243491908759 : ℤ)⟩ := by
  rfl

theorem ev_S1a : (JS1a).value = ⟨(193 : ℤ), (834921151353883932529770099404527257847409233631553848433910 : ℤ), (873263399515626642607577567178194667666287926636243491908759 : ℤ)⟩ := by
  rw [show (JS1a).value = dAdd (JX4X5).value (JX4X6).value from rfl, ev_X4X5, ev_X4X6]
  exact op_S1a

theorem p0_S1a : (JS1a).part 0 = ⟨(194 : ℤ), (1325271668815688781793285872070678187059379735923101346720493 : ℤ), (1386132380183193298773532333944367908601909857407509698193273 : ℤ)⟩ := by
  rw [show (JS1a).part 0 = dAdd ((JX4X5).part 0) ((JX4X6).part 0) from rfl, p0_X4X5, p0_X4X6]
  rfl

theorem p1_S1a : (JS1a).part 1 = ⟨(195 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rw [show (JS1a).part 1 = dAdd ((JX4X5).part 1) ((JX4X6).part 1) from rfl, p1_X4X5, p1_X4X6]
  rfl

theorem p2_S1a : (JS1a).part 2 = ⟨(195 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391381 : ℤ)⟩ := by
  rw [show (JS1a).part 2 = dAdd ((JX4X5).part 2) ((JX4X6).part 2) from rfl, p2_X4X5, p2_X4X6]
  rfl

def JS1 : DCJet := DCJetKit.add JS1a JX5X6
theorem JS1_mem : JetMem JS1 fS1 D :=
  DCJetKit.add_mem (JS1a_mem) (JX5X6_mem)

theorem op_S1 : dAdd ⟨(193 : ℤ), (834921151353883932529770099404527257847409233631553848433910 : ℤ), (873263399515626642607577567178194667666287926636243491908759 : ℤ)⟩ ⟨(195 : ℤ), (1376729461015220005016887581010995972280086956417868416471207 : ℤ), (1505975819319029734400390200144498260173956375031885250841254 : ℤ)⟩ = ⟨(193 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ := by
  rfl

theorem ev_S1 : (JS1).value = ⟨(193 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ := by
  rw [show (JS1).value = dAdd (JS1a).value (JX5X6).value from rfl, ev_S1a, ev_X5X6]
  exact op_S1

theorem p0_S1 : (JS1).part 0 = ⟨(194 : ℤ), (1325271668815688781793285872070678187059379735923101346720493 : ℤ), (1386132380183193298773532333944367908601909857407509698193273 : ℤ)⟩ := by
  rw [show (JS1).part 0 = dAdd ((JS1a).part 0) ((JX5X6).part 0) from rfl, p0_S1a, p0_X5X6]
  rfl

theorem p1_S1 : (JS1).part 1 = ⟨(194 : ℤ), (1330692086869348422683784731146247067408369635276912520147744 : ℤ), (1389134475247151341664146061049827287463102898319903916535004 : ℤ)⟩ := by
  rw [show (JS1).part 1 = dAdd ((JS1a).part 1) ((JX5X6).part 1) from rfl, p1_S1a, p1_X5X6]
  rfl

theorem p2_S1 : (JS1).part 2 = ⟨(194 : ℤ), (1332079688075401346775576788609585941566046787436028466492541 : ℤ), (1390539045679706168059427704157739230195178749500160032274216 : ℤ)⟩ := by
  rw [show (JS1).part 2 = dAdd ((JS1a).part 2) ((JX5X6).part 2) from rfl, p2_S1a, p2_X5X6]
  rfl

def JCN2S2 : DCJet := DCJetKit.mul JCN2 JS2
theorem JCN2S2_mem : JetMem JCN2S2 fCN2S2 D :=
  DCJetKit.mul_mem (JCN2_mem D) (JS2_mem)

theorem op_CN2S2 : dMul ⟨(0 : ℤ), (-2 : ℤ), (-2 : ℤ)⟩ ⟨(193 : ℤ), (1194807040559551540723191842791251136650528195553366636227065 : ℤ), (1259550125686841124643446839970228905803821766996277430988786 : ℤ)⟩ = ⟨(192 : ℤ), (-1259550125686841124643446839970228905803821766996277430988786 : ℤ), (-1194807040559551540723191842791251136650528195553366636227065 : ℤ)⟩ := by
  rfl

theorem ev_CN2S2 : (JCN2S2).value = ⟨(192 : ℤ), (-1259550125686841124643446839970228905803821766996277430988786 : ℤ), (-1194807040559551540723191842791251136650528195553366636227065 : ℤ)⟩ := by
  rw [show (JCN2S2).value = dMul (JCN2).value (JS2).value from rfl, ev_CN2, ev_S2]
  exact op_CN2S2

theorem p0_CN2S2 : (JCN2S2).part 0 = ⟨(192 : ℤ), (-803620074306248669274587468256498742518912889424023852370967 : ℤ), (-803620074305655482856881990607261370545738583972812000177204 : ℤ)⟩ := by
  rw [show (JCN2S2).part 0 = dAdd (dMul (JCN2).value ((JS2).part 0)) (dMul (JS2).value ((JCN2).part 0)) from rfl, ev_CN2, ev_S2, p0_CN2, p0_S2]
  rfl

theorem p1_CN2S2 : (JCN2S2).part 1 = ⟨(193 : ℤ), (-1260951819482331590446277711936573835542758467346198814066447 : ℤ), (-1183912630793926101121210235008664552626970420449296463240887 : ℤ)⟩ := by
  rw [show (JCN2S2).part 1 = dAdd (dMul (JCN2).value ((JS2).part 1)) (dMul (JS2).value ((JCN2).part 1)) from rfl, ev_CN2, ev_S2, p1_CN2, p1_S2]
  rfl

theorem p2_CN2S2 : (JCN2S2).part 2 = ⟨(193 : ℤ), (-1313751043305869213046764753546432444449075019647790757471160 : ℤ), (-1223032009872520673839499211475121560678085775352331361294972 : ℤ)⟩ := by
  rw [show (JCN2S2).part 2 = dAdd (dMul (JCN2).value ((JS2).part 2)) (dMul (JS2).value ((JCN2).part 2)) from rfl, ev_CN2, ev_S2, p2_CN2, p2_S2]
  rfl

def JC4S1 : DCJet := DCJetKit.mul JC4 JS1
theorem JC4S1_mem : JetMem JC4S1 fC4S1 D :=
  DCJetKit.mul_mem (JC4_mem D) (JS1_mem)

theorem op_C4S1 : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(193 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ = ⟨(191 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ := by
  rfl

theorem ev_C4S1 : (JC4S1).value = ⟨(191 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ := by
  rw [show (JC4S1).value = dMul (JC4).value (JS1).value from rfl, ev_C4, ev_S1]
  exact op_C4S1

theorem p0_C4S1 : (JC4S1).part 0 = ⟨(192 : ℤ), (1325271668815688781793285872070678187059379735923101346720493 : ℤ), (1386132380183193298773532333944367908601909857407509698193273 : ℤ)⟩ := by
  rw [show (JC4S1).part 0 = dAdd (dMul (JC4).value ((JS1).part 0)) (dMul (JS1).value ((JC4).part 0)) from rfl, ev_C4, ev_S1, p0_C4, p0_S1]
  rfl

theorem p1_C4S1 : (JC4S1).part 1 = ⟨(192 : ℤ), (1330692086869348422683784731146247067408369635276912520147744 : ℤ), (1389134475247151341664146061049827287463102898319903916535004 : ℤ)⟩ := by
  rw [show (JC4S1).part 1 = dAdd (dMul (JC4).value ((JS1).part 1)) (dMul (JS1).value ((JC4).part 1)) from rfl, ev_C4, ev_S1, p1_C4, p1_S1]
  rfl

theorem p2_C4S1 : (JC4S1).part 2 = ⟨(192 : ℤ), (1332079688075401346775576788609585941566046787436028466492541 : ℤ), (1390539045679706168059427704157739230195178749500160032274216 : ℤ)⟩ := by
  rw [show (JC4S1).part 2 = dAdd (dMul (JC4).value ((JS1).part 2)) (dMul (JS1).value ((JC4).part 2)) from rfl, ev_C4, ev_S1, p2_C4, p2_S1]
  rfl

def JDltA : DCJet := DCJetKit.add JCN2S2 JC4S1
theorem JDltA_mem : JetMem JDltA fDltA D :=
  DCJetKit.add_mem (JCN2S2_mem) (JC4S1_mem)

theorem op_DltA : dAdd ⟨(192 : ℤ), (-1259550125686841124643446839970228905803821766996277430988786 : ℤ), (-1194807040559551540723191842791251136650528195553366636227065 : ℤ)⟩ ⟨(191 : ℤ), (1179103516607688933783991994657276250917430972736020952551711 : ℤ), (1249757354345384076207675117214319232709777020394214804619073 : ℤ)⟩ = ⟨(192 : ℤ), (1098656907528536742924537149344323596031040178475764474114636 : ℤ), (1304707668131216611692158391637387328769025845235062973011081 : ℤ)⟩ := by
  rfl

theorem ev_DltA : (JDltA).value = ⟨(192 : ℤ), (1098656907528536742924537149344323596031040178475764474114636 : ℤ), (1304707668131216611692158391637387328769025845235062973011081 : ℤ)⟩ := by
  rw [show (JDltA).value = dAdd (JCN2S2).value (JC4S1).value from rfl, ev_CN2S2, ev_C4S1]
  exact op_DltA

theorem p0_DltA : (JDltA).part 0 = ⟨(192 : ℤ), (521651594509440112518698403814179444540466846499077494349526 : ℤ), (582512305877537815916650343337106538056171273434697698016069 : ℤ)⟩ := by
  rw [show (JDltA).part 0 = dAdd ((JCN2S2).part 0) ((JC4S1).part 0) from rfl, p0_CN2S2, p0_C4S1]
  rfl

theorem p1_DltA : (JDltA).part 1 = ⟨(193 : ℤ), (1400432354256365254921291750355920299273980803207626226229041 : ℤ), (1594356319700376582207081887090990022299235376190511369829121 : ℤ)⟩ := by
  rw [show (JDltA).part 1 = dAdd ((JCN2S2).part 1) ((JC4S1).part 1) from rfl, p1_CN2S2, p1_C4S1]
  rfl

theorem p2_DltA : (JDltA).part 2 = ⟨(193 : ℤ), (1350408332844933480504388823672739438683018555224266175513922 : ℤ), (1558046081486891662279356196840356899712271723647988703253460 : ℤ)⟩ := by
  rw [show (JDltA).part 2 = dAdd ((JCN2S2).part 2) ((JC4S1).part 2) from rfl, p2_CN2S2, p2_C4S1]
  rfl

def JX4X5X6 : DCJet := DCJetKit.mul JX4X5 JX6
theorem JX4X5X6_mem : JetMem JX4X5X6 fX4X5X6 D :=
  DCJetKit.mul_mem (JX4X5_mem) (JX6_mem)

theorem op_X4X5X6 : dMul ⟨(194 : ℤ), (825874219863129527960407603870867911761373774876214810262600 : ℤ), (861323841570679806312249620866416671588236940392648069160396 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(192 : ℤ), (1092847846153881639982405361806528602795933026004503948994842 : ℤ), (1195443605376034075272646473099984287782416641260069032123654 : ℤ)⟩ := by
  rfl

theorem ev_X4X5X6 : (JX4X5X6).value = ⟨(192 : ℤ), (1092847846153881639982405361806528602795933026004503948994842 : ℤ), (1195443605376034075272646473099984287782416641260069032123654 : ℤ)⟩ := by
  rw [show (JX4X5X6).value = dMul (JX4X5).value (JX6).value from rfl, ev_X4X5, ev_X6]
  exact op_X4X5X6

theorem p0_X4X5X6 : (JX4X5X6).part 0 = ⟨(192 : ℤ), (867339560439588603160639176036927462536454782543257102376859 : ℤ), (948764766171222173983998468890163308394516914945397273007685 : ℤ)⟩ := by
  rw [show (JX4X5X6).part 0 = dAdd (dMul (JX4X5).value ((JX6).part 0)) (dMul (JX6).value ((JX4X5).part 0)) from rfl, ev_X4X5, ev_X6, p0_X4X5, p0_X6]
  rfl

theorem p1_X4X5X6 : (JX4X5X6).part 1 = ⟨(192 : ℤ), (960379457068602520630573076942085085090022188777367376764992 : ℤ), (1028693450429327891773811204301908687447843497564432514023399 : ℤ)⟩ := by
  rw [show (JX4X5X6).part 1 = dAdd (dMul (JX4X5).value ((JX6).part 1)) (dMul (JX6).value ((JX4X5).part 1)) from rfl, ev_X4X5, ev_X6, p1_X4X5, p1_X6]
  rfl

theorem p2_X4X5X6 : (JX4X5X6).part 2 = ⟨(192 : ℤ), (950028874493527380189229352506511970860721364263040224280130 : ℤ), (1014723646400136594468314077252080593139565670448767253662312 : ℤ)⟩ := by
  rw [show (JX4X5X6).part 2 = dAdd (dMul (JX4X5).value ((JX6).part 2)) (dMul (JX6).value ((JX4X5).part 2)) from rfl, ev_X4X5, ev_X6, p2_X4X5, p2_X6]
  rfl


/-! ## 3b. The `Dlt` corner rule (box pass)

`fDlt` is nonincreasing in each coordinate on the wt1 box (landed
`Kepler.NliBanks21.nb21_delta_mono_y4/y5/y6`), so its range on `D` is bracketed
by the two opposite corner values (`(+ + +)` is the minimum).  The naive DC
interval of the `Dlt` subtree straddles zero, which makes every `matan` gate
false; the corner bracket replaces only the *value* channel, the AD partial
channel is unchanged. -/
def xlo : Fin 3 → ℝ
  | 0 => (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)
  | 1 => (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s)
  | 2 => (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s)

def xhi : Fin 3 → ℝ
  | 0 => (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s)
  | 1 => (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s)
  | 2 => (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s)

theorem fDlt_eq_delta (y : Fin 3 → ℝ) :
    fDlt y = deltaX (y 0 * y 0) 2 (y 1 * y 1) 2 (y 2 * y 2) 2 := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4]
  unfold deltaX
  ring

theorem fDlt_xlo : fDlt xlo = (193528914514688597829235965451697643819024591216842407022507832940758917217370089108404842331800737094333739908746348906148538806906754334970128201597317958077320013146235356209005031907185076999573288675704381468489924496890605544875798363265151646919085483633798176656344471628592923746703378672613549650218838932230698978924488076168430959096114973480992691824 : ℝ) * (2 : ℝ) ^ (-(1200 : ℤ)) := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4, xlo, s]
  norm_num

theorem fDlt_xhi : fDlt xhi = (122123803465304435472251751013714728896247800862018753320651292980945244343916313798521754016871242267047625921216933007260377695914635320115357461108028126647349573431097395289103868087072344773329931875128854081266222617064762661103777662499231465809399679025575018805111817940050368013215982390597276719921339599625530302306848805779262269117303382186793495932 : ℝ) * (2 : ℝ) ^ (-(1200 : ℤ)) := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4, xhi, s]
  norm_num

/-- The corner bracket of `fDlt` on `D`, on the same `2^-200` grid as the box. -/
def DltCorner : DC := ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩

theorem fDlt_le_xlo : ∀ x ∈ D, fDlt x ≤ fDlt xlo := by
  intro x hx
  obtain ⟨hx4, hx5, hx6⟩ := hx
  have hx4lo : (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) ≤ x 0 := hx4.1
  have hx5lo : (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s) ≤ x 1 := hx5.1
  have hx6lo : (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s) ≤ x 2 := hx6.1
  have hhm : 2 * hminus ≤ 2.46352 := Kepler.NliBanks17.nb17_two_hminus_bounds.2
  have hc4 : (2.46352 : ℝ) ≤ (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc5 : (2 : ℝ) ≤ (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc6 : (2 : ℝ) ≤ (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s) := by norm_num [s]
  have h4lo : 2 * hminus ≤ (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) := hhm.trans hc4
  have h4x : 2 * hminus ≤ x 0 := h4lo.trans hx4lo
  have h5x : (2 : ℝ) ≤ x 1 := hc5.trans hx5lo
  have h6x : (2 : ℝ) ≤ x 2 := hc6.trans hx6lo
  calc fDlt x = deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 := fDlt_eq_delta x
    _ ≤ deltaX ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) * (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y4 (y4 := (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) (y4' := x 0) h4lo h4x hx4lo h5x h6x
    _ ≤ deltaX ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) * (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) 2 ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s) * (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s)) 2 (x 2 * x 2) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y5 (y4 := (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) (y5 := x 1) (y5' := (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s)) h4lo h5x hc5 hx5lo h6x
    _ ≤ deltaX ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) * (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) 2 ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s) * (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s)) 2 ((((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s) * (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s)) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y6 (y4 := (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s)) (y6 := x 2) (y6' := (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s)) h4lo h6x hc6 hx6lo hc5
    _ = fDlt xlo := (fDlt_eq_delta xlo).symm

theorem fDlt_xhi_le : ∀ x ∈ D, fDlt xhi ≤ fDlt x := by
  intro x hx
  obtain ⟨hx4, hx5, hx6⟩ := hx
  have hx4hi : x 0 ≤ (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s) := hx4.2
  have hx5hi : x 1 ≤ (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s) := hx5.2
  have hx6hi : x 2 ≤ (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) := hx6.2
  have hhm : 2 * hminus ≤ 2.46352 := Kepler.NliBanks17.nb17_two_hminus_bounds.2
  have hc4 : (2.46352 : ℝ) ≤ (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc4h : (2.46352 : ℝ) ≤ (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc5 : (2 : ℝ) ≤ (((3657176895331534926107553882173950532625280555789666908403972 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc5h : (2 : ℝ) ≤ (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc6 : (2 : ℝ) ≤ (((3697021906849702090774160988178878465989773336804422257896241 : ℤ) : ℝ) * s) := by norm_num [s]
  have hc6h : (2 : ℝ) ≤ (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) := by norm_num [s]
  have h4lo : 2 * hminus ≤ (((4049483871532655494365744472699729758355951544332637944959467 : ℤ) : ℝ) * s) := hhm.trans hc4
  have h4x : 2 * hminus ≤ x 0 := h4lo.trans hx4.1
  have h4hi : 2 * hminus ≤ (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s) := hhm.trans hc4h
  have h5x : (2 : ℝ) ≤ x 1 := hc5.trans hx5.1
  have h5hi : (2 : ℝ) ≤ (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s) := hc5h
  have h6x : (2 : ℝ) ≤ x 2 := hc6.trans hx6.1
  have h6hi : (2 : ℝ) ≤ (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) := hc6h
  calc fDlt xhi = deltaX ((((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s) * (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s)) 2 ((((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s) * (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s)) 2 ((((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) * (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s)) 2 := fDlt_eq_delta xhi
    _ ≤ deltaX (x 0 * x 0) 2 ((((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s) * (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s)) 2 ((((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) * (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s)) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y4 (y4 := x 0) (y4' := (((4049483871533651860230706817030176796531686758792705811703733 : ℤ) : ℝ) * s)) h4x h4hi hx4hi h5hi h6hi
    _ ≤ deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 ((((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s) * (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s)) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y5 (y4 := x 0) (y5 := (((3734842111502011420851541171028160066896758316960222749146863 : ℤ) : ℝ) * s)) (y5' := x 1) h4x h5hi h5x hx5hi h6hi
    _ ≤ deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 :=
        Kepler.NliBanks21.nb21_delta_mono_y6 (y4 := x 0) (y6 := (((3786260064126602103902664808873744373940916659619106874140858 : ℤ) : ℝ) * s)) (y6' := x 2) h4x h6hi h6x hx6hi h5x
    _ = fDlt x := (fDlt_eq_delta x).symm

theorem DltCorner_mem : ∀ x ∈ D, DltCorner.mem (fDlt x) := by
  intro x hx
  have h1 := fDlt_xhi_le x hx
  have h2 := fDlt_le_xlo x hx
  rw [fDlt_xhi] at h1
  rw [fDlt_xlo] at h2
  have c1 : ((11397370272740595839809771867756869589328801928213285408180684 : ℤ) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
      (122123803465304435472251751013714728896247800862018753320651292980945244343916313798521754016871242267047625921216933007260377695914635320115357461108028126647349573431097395289103868087072344773329931875128854081266222617064762661103777662499231465809399679025575018805111817940050368013215982390597276719921339599625530302306848805779262269117303382186793495932 : ℝ) * (2 : ℝ) ^ (-(1200 : ℤ)) := by norm_num
  have c2 : (193528914514688597829235965451697643819024591216842407022507832940758917217370089108404842331800737094333739908746348906148538806906754334970128201597317958077320013146235356209005031907185076999573288675704381468489924496890605544875798363265151646919085483633798176656344471628592923746703378672613549650218838932230698978924488076168430959096114973480992691824 : ℝ) * (2 : ℝ) ^ (-(1200 : ℤ)) ≤
      ((18061349504497839836771016887493827171430585322027857889667964 : ℤ) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) := by norm_num
  exact ⟨c1.trans h1, h2.trans c2⟩

def JDltN : DCJet := DCJetKit.sub JDltA JX4X5X6
theorem JDltN_mem : JetMem JDltN fDlt D :=
  DCJetKit.sub_mem (JDltA_mem) (JX4X5X6_mem)

def JDlt : DCJet := ⟨DltCorner, JDltN.part⟩
theorem JDlt_mem : JetMem JDlt fDlt D := by
  refine ⟨JDltN_mem.1, ?_, ?_⟩
  · simpa [JDlt] using DltCorner_mem
  · intro x hx i
    simpa [JDlt] using JDltN_mem.2.2 x hx i

theorem ev_Dlt : (JDlt).value = ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ := by rfl

theorem p0_DltN : (JDltN).part 0 =
    dAdd ((JDltA).part 0) (dNeg ((JX4X5X6).part 0)) := by rfl

theorem p0_Dlt : (JDlt).part 0 = ⟨(192 : ℤ), (-427113171661782061465300065075983863854050068446319778658159 : ℤ), (-284827254562050787243988832699820924480283509108559404360790 : ℤ)⟩ := by
  rw [show (JDlt).part 0 = (JDltN).part 0 from rfl, p0_DltN, p0_DltA, p0_X4X5X6]
  rfl

theorem p1_DltN : (JDltN).part 1 =
    dAdd ((JDltA).part 1) (dNeg ((JX4X5X6).part 1)) := by rfl

theorem p1_Dlt : (JDlt).part 1 = ⟨(193 : ℤ), (-656954546602290528626330658247897075621706191921238801817757 : ℤ), (-326402594436828459054064266793180147880809001364223383700863 : ℤ)⟩ := by
  rw [show (JDlt).part 1 = (JDltN).part 1 from rfl, p1_DltN, p1_DltA, p1_X4X5X6]
  rfl

theorem p2_DltN : (JDltN).part 2 =
    dAdd ((JDltA).part 2) (dNeg ((JX4X5X6).part 2)) := by rfl

theorem p2_Dlt : (JDlt).part 2 = ⟨(193 : ℤ), (-679038959955339708432239330831421747596112785673268331810702 : ℤ), (-342011667500163098099102508172667042009171004878091745306800 : ℤ)⟩ := by
  rw [show (JDlt).part 2 = (JDltN).part 2 from rfl, p2_DltN, p2_DltA, p2_X4X5X6]
  rfl


def JSIY5 : DCJet := DCJetKit.mul JSI JY5
theorem JSIY5_mem : JetMem JSIY5 fSIY5 D :=
  DCJetKit.mul_mem (JSI_mem D) (JY5_mem)

theorem op_SIY5 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968852 : ℤ)⟩ := by
  rfl

theorem ev_SIY5 : (JSIY5).value = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968852 : ℤ)⟩ := by
  rw [show (JSIY5).value = dMul (JSI).value (JY5).value from rfl, ev_SI, ev_Y5]
  exact op_SIY5

theorem p0_SIY5 : (JSIY5).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY5).part 0 = dAdd (dMul (JSI).value ((JY5).part 0)) (dMul (JY5).value ((JSI).part 0)) from rfl, ev_SI, ev_Y5, p0_SI, p0_Y5]
  rfl

theorem p1_SIY5 : (JSIY5).part 1 = ⟨(199 : ℤ), (1136276788042180457691927808607832267993707273715849875161088 : ℤ), (1136276788042180458388826096061914241166698469736111172222976 : ℤ)⟩ := by
  rw [show (JSIY5).part 1 = dAdd (dMul (JSI).value ((JY5).part 1)) (dMul (JY5).value ((JSI).part 1)) from rfl, ev_SI, ev_Y5, p1_SI, p1_Y5]
  rfl

theorem p2_SIY5 : (JSIY5).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY5).part 2 = dAdd (dMul (JSI).value ((JY5).part 2)) (dMul (JY5).value ((JSI).part 2)) from rfl, ev_SI, ev_Y5, p2_SI, p2_Y5]
  rfl

def JSIY5Y4 : DCJet := DCJetKit.mul JSIY5 JY4
theorem JSIY5Y4_mem : JetMem JSIY5Y4 fSIY5Y4 D :=
  DCJetKit.mul_mem (JSIY5_mem) (JY4_mem)

theorem op_SIY5Y4 : dMul ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968852 : ℤ)⟩ ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ = ⟨(196 : ℤ), (814594593546623258663716959008037713265529015706666181331050 : ℤ), (831893637867013800718682824121088886580911539198386999231183 : ℤ)⟩ := by
  rfl

theorem ev_SIY5Y4 : (JSIY5Y4).value = ⟨(196 : ℤ), (814594593546623258663716959008037713265529015706666181331050 : ℤ), (831893637867013800718682824121088886580911539198386999231183 : ℤ)⟩ := by
  rw [show (JSIY5Y4).value = dMul (JSIY5).value (JY4).value from rfl, ev_SIY5, ev_Y4]
  exact op_SIY5Y4

theorem p0_SIY5Y4 : (JSIY5Y4).part 0 = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968852 : ℤ)⟩ := by
  rw [show (JSIY5Y4).part 0 = dAdd (dMul (JSIY5).value ((JY4).part 0)) (dMul (JY4).value ((JSIY5).part 0)) from rfl, ev_SIY5, ev_Y4, p0_SIY5, p0_Y4]
  rfl

theorem p1_SIY5Y4 : (JSIY5Y4).part 1 = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702970 : ℤ), (1431708752933499646099749717823721647736341186520546576860538 : ℤ)⟩ := by
  rw [show (JSIY5Y4).part 1 = dAdd (dMul (JSIY5).value ((JY4).part 1)) (dMul (JY4).value ((JSIY5).part 1)) from rfl, ev_SIY5, ev_Y4, p1_SIY5, p1_Y4]
  rfl

theorem p2_SIY5Y4 : (JSIY5Y4).part 2 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY5Y4).part 2 = dAdd (dMul (JSIY5).value ((JY4).part 2)) (dMul (JY4).value ((JSIY5).part 2)) from rfl, ev_SIY5, ev_Y4, p2_SIY5, p2_Y4]
  rfl

def JY5X4 : DCJet := DCJetKit.mul JY5 JX4
theorem JY5X4_mem : JetMem JY5X4 fY5X4 D :=
  DCJetKit.mul_mem (JY5_mem) (JX4_mem)

theorem op_Y5X4 : dMul ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ = ⟨(196 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rfl

theorem ev_Y5X4 : (JY5X4).value = ⟨(196 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rw [show (JY5X4).value = dMul (JY5).value (JX4).value from rfl, ev_Y5, ev_X4]
  exact op_Y5X4

theorem p0_Y5X4 : (JY5X4).part 0 = ⟨(196 : ℤ), (1152010722029433501723879472884794417776963375073745076147250 : ℤ), (1176475265123423066506087432269043519770939407388454999234619 : ℤ)⟩ := by
  rw [show (JY5X4).part 0 = dAdd (dMul (JY5).value ((JX4).part 0)) (dMul (JX4).value ((JY5).part 0)) from rfl, ev_Y5, ev_X4, p0_Y5, p0_X4]
  rfl

theorem p1_Y5X4 : (JY5X4).part 1 = ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JY5X4).part 1 = dAdd (dMul (JY5).value ((JX4).part 1)) (dMul (JX4).value ((JY5).part 1)) from rfl, ev_Y5, ev_X4, p1_Y5, p1_X4]
  rfl

theorem p2_Y5X4 : (JY5X4).part 2 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5X4).part 2 = dAdd (dMul (JY5).value ((JX4).part 2)) (dMul (JX4).value ((JY5).part 2)) from rfl, ev_Y5, ev_X4, p2_Y5, p2_X4]
  rfl

def JY5X4CH : DCJet := DCJetKit.mul JY5X4 JCH
theorem JY5X4CH_mem : JetMem JY5X4CH fY5X4CH D :=
  DCJetKit.mul_mem (JY5X4_mem) (JCH_mem D)

theorem op_Y5X4CH : dMul ⟨(196 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rfl

theorem ev_Y5X4CH : (JY5X4CH).value = ⟨(197 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rw [show (JY5X4CH).value = dMul (JY5X4).value (JCH).value from rfl, ev_Y5X4, ev_CH]
  exact op_Y5X4CH

theorem p0_Y5X4CH : (JY5X4CH).part 0 = ⟨(197 : ℤ), (1152010722029433501723879472884794417776963375073745076147250 : ℤ), (1176475265123423066506087432269043519770939407388454999234619 : ℤ)⟩ := by
  rw [show (JY5X4CH).part 0 = dAdd (dMul (JY5X4).value ((JCH).part 0)) (dMul (JCH).value ((JY5X4).part 0)) from rfl, ev_Y5X4, ev_CH, p0_Y5X4, p0_CH]
  rfl

theorem p1_Y5X4CH : (JY5X4CH).part 1 = ⟨(198 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JY5X4CH).part 1 = dAdd (dMul (JY5X4).value ((JCH).part 1)) (dMul (JCH).value ((JY5X4).part 1)) from rfl, ev_Y5X4, ev_CH, p1_Y5X4, p1_CH]
  rfl

theorem p2_Y5X4CH : (JY5X4CH).part 2 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5X4CH).part 2 = dAdd (dMul (JY5X4).value ((JCH).part 2)) (dMul (JCH).value ((JY5X4).part 2)) from rfl, ev_Y5X4, ev_CH, p2_Y5X4, p2_CH]
  rfl

def JA1 : DCJet := DCJetKit.add JSIY5Y4 JY5X4CH
theorem JA1_mem : JetMem JA1 fA1 D :=
  DCJetKit.add_mem (JSIY5Y4_mem) (JY5X4CH_mem)

theorem op_A1 : dAdd ⟨(196 : ℤ), (814594593546623258663716959008037713265529015706666181331050 : ℤ), (831893637867013800718682824121088886580911539198386999231183 : ℤ)⟩ ⟨(197 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ = ⟨(196 : ℤ), (1540361348425166364749761026925458196465015942003125579303817 : ℤ), (1573073054894952698048364688260125412649479390289113342066533 : ℤ)⟩ := by
  rfl

theorem ev_A1 : (JA1).value = ⟨(196 : ℤ), (1540361348425166364749761026925458196465015942003125579303817 : ℤ), (1573073054894952698048364688260125412649479390289113342066533 : ℤ)⟩ := by
  rw [show (JA1).value = dAdd (JSIY5Y4).value (JY5X4CH).value from rfl, ev_SIY5Y4, ev_Y5X4CH]
  exact op_A1

theorem p0_A1 : (JA1).part 0 = ⟨(196 : ℤ), (899257183850678361442779799540824872882739233452216260824042 : ℤ), (918354155524731023439466269117217671449422143545569121109523 : ℤ)⟩ := by
  rw [show (JA1).part 0 = dAdd ((JSIY5Y4).part 0) ((JY5X4CH).part 0) from rfl, p0_SIY5Y4, p0_Y5X4CH]
  rfl

theorem p1_A1 : (JA1).part 1 = ⟨(197 : ℤ), (1353648086232966928708519273873141765777097950673375897682600 : ℤ), (1353648086233456918659942790437827259787838219696432047964728 : ℤ)⟩ := by
  rw [show (JA1).part 1 = dAdd ((JSIY5Y4).part 1) ((JY5X4CH).part 1) from rfl, p1_SIY5Y4, p1_Y5X4CH]
  rfl

theorem p2_A1 : (JA1).part 2 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JA1).part 2 = dAdd ((JSIY5Y4).part 2) ((JY5X4CH).part 2) from rfl, p2_SIY5Y4, p2_Y5X4CH]
  rfl

def JX5X4 : DCJet := DCJetKit.add JX5 JX4
theorem JX5X4_mem : JetMem JX5X4 fX5X4 D :=
  DCJetKit.add_mem (JX5_mem) (JX4_mem)

theorem op_X5X4 : dAdd ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ = ⟨(196 : ℤ), (1157996670123617684782110677775269109756238593274097965788536 : ℤ), (1180325733935424627073506422634191877438580894456801883367027 : ℤ)⟩ := by
  rfl

theorem ev_X5X4 : (JX5X4).value = ⟨(196 : ℤ), (1157996670123617684782110677775269109756238593274097965788536 : ℤ), (1180325733935424627073506422634191877438580894456801883367027 : ℤ)⟩ := by
  rw [show (JX5X4).value = dAdd (JX5).value (JX4).value from rfl, ev_X5, ev_X4]
  exact op_X5X4

theorem p0_X5X4 : (JX5X4).part 0 = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JX5X4).part 0 = dAdd ((JX5).part 0) ((JX4).part 0) from rfl, p0_X5, p0_X4]
  rfl

theorem p1_X5X4 : (JX5X4).part 1 = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JX5X4).part 1 = dAdd ((JX5).part 1) ((JX4).part 1) from rfl, p1_X5, p1_X4]
  rfl

theorem p2_X5X4 : (JX5X4).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX5X4).part 2 = dAdd ((JX5).part 2) ((JX4).part 2) from rfl, p2_X5, p2_X4]
  rfl

def JQA : DCJet := DCJetKit.sub JX5X4 JX6
theorem JQA_mem : JetMem JQA fQA D :=
  DCJetKit.sub_mem (JX5X4_mem) (JX6_mem)

theorem op_QA : dAdd ⟨(196 : ℤ), (1157996670123617684782110677775269109756238593274097965788536 : ℤ), (1180325733935424627073506422634191877438580894456801883367027 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩) = ⟨(197 : ℤ), (1200847261310301790901092728145981099641791809959357020890312 : ℤ), (1297451565068331822679221720377748073429133705785746766727475 : ℤ)⟩ := by
  rfl

theorem ev_QA : (JQA).value = ⟨(197 : ℤ), (1200847261310301790901092728145981099641791809959357020890312 : ℤ), (1297451565068331822679221720377748073429133705785746766727475 : ℤ)⟩ := by
  rw [show (JQA).value = dAdd (JX5X4).value (dNeg (JX6).value) from rfl, ev_X5X4, ev_X6]
  exact op_QA

theorem p0_QA : (JQA).part 0 = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JQA).part 0 = dAdd ((JX5X4).part 0) (dNeg ((JX6).part 0)) from rfl, p0_X5X4, p0_X6]
  rfl

theorem p1_QA : (JQA).part 1 = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JQA).part 1 = dAdd ((JX5X4).part 1) (dNeg ((JX6).part 1)) from rfl, p1_X5X4, p1_X6]
  rfl

theorem p2_QA : (JQA).part 2 = ⟨(197 : ℤ), (-946565016031650525975666202218436093485229164904776718535215 : ℤ), (-924255476712425522693540247044719616497443334201105564474060 : ℤ)⟩ := by
  rw [show (JQA).part 2 = dAdd ((JX5X4).part 2) (dNeg ((JX6).part 2)) from rfl, p2_X5X4, p2_X6]
  rfl

def JSIQA : DCJet := DCJetKit.mul JSI JQA
theorem JSIQA_mem : JetMem JSIQA fSIQA D :=
  DCJetKit.mul_mem (JSI_mem D) (JQA_mem)

theorem op_SIQA : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (1200847261310301790901092728145981099641791809959357020890312 : ℤ), (1297451565068331822679221720377748073429133705785746766727475 : ℤ)⟩ = ⟨(196 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ := by
  rfl

theorem ev_SIQA : (JSIQA).value = ⟨(196 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ := by
  rw [show (JSIQA).value = dMul (JSI).value (JQA).value from rfl, ev_SI, ev_QA]
  exact op_SIQA

theorem p0_SIQA : (JSIQA).part 0 = ⟨(197 : ℤ), (1431708752933147376691829038845868657672071164881970842702969 : ℤ), (1431708752933499646099749717823721647736341186520546576860539 : ℤ)⟩ := by
  rw [show (JSIQA).part 0 = dAdd (dMul (JSI).value ((JQA).part 0)) (dMul (JQA).value ((JSI).part 0)) from rfl, ev_SI, ev_QA, p0_SI, p0_QA]
  rfl

theorem p1_SIQA : (JSIQA).part 1 = ⟨(197 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968853 : ℤ)⟩ := by
  rw [show (JSIQA).part 1 = dAdd (dMul (JSI).value ((JQA).part 1)) (dMul (JQA).value ((JSI).part 1)) from rfl, ev_SI, ev_QA, p1_SI, p1_QA]
  rfl

theorem p2_SIQA : (JSIQA).part 2 = ⟨(197 : ℤ), (-1338645083339866316304152055976740378476713367221754583465239 : ℤ), (-1307094630264322489861532060983251100096908089715760200851474 : ℤ)⟩ := by
  rw [show (JSIQA).part 2 = dAdd (dMul (JSI).value ((JQA).part 2)) (dMul (JQA).value ((JSI).part 2)) from rfl, ev_SI, ev_QA, p2_SI, p2_QA]
  rfl

def JSIQACH : DCJet := DCJetKit.mul JSIQA JCH
theorem JSIQACH_mem : JetMem JSIQACH fSIQACH D :=
  DCJetKit.mul_mem (JSIQA_mem) (JCH_mem D)

theorem op_SIQACH : dMul ⟨(196 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ := by
  rfl

theorem ev_SIQACH : (JSIQACH).value = ⟨(197 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ := by
  rw [show (JSIQACH).value = dMul (JSIQA).value (JCH).value from rfl, ev_SIQA, ev_CH]
  exact op_SIQACH

theorem p0_SIQACH : (JSIQACH).part 0 = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702969 : ℤ), (1431708752933499646099749717823721647736341186520546576860539 : ℤ)⟩ := by
  rw [show (JSIQACH).part 0 = dAdd (dMul (JSIQA).value ((JCH).part 0)) (dMul (JCH).value ((JSIQA).part 0)) from rfl, ev_SIQA, ev_CH, p0_SIQA, p0_CH]
  rfl

theorem p1_SIQACH : (JSIQACH).part 1 = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968853 : ℤ)⟩ := by
  rw [show (JSIQACH).part 1 = dAdd (dMul (JSIQA).value ((JCH).part 1)) (dMul (JCH).value ((JSIQA).part 1)) from rfl, ev_SIQA, ev_CH, p1_SIQA, p1_CH]
  rfl

theorem p2_SIQACH : (JSIQACH).part 2 = ⟨(198 : ℤ), (-1338645083339866316304152055976740378476713367221754583465239 : ℤ), (-1307094630264322489861532060983251100096908089715760200851474 : ℤ)⟩ := by
  rw [show (JSIQACH).part 2 = dAdd (dMul (JSIQA).value ((JCH).part 2)) (dMul (JCH).value ((JSIQA).part 2)) from rfl, ev_SIQA, ev_CH, p2_SIQA, p2_CH]
  rfl

def JA2 : DCJet := DCJetKit.add JA1 JSIQACH
theorem JA2_mem : JetMem JA2 fA2 D :=
  DCJetKit.add_mem (JA1_mem) (JSIQACH_mem)

theorem op_A2 : dAdd ⟨(196 : ℤ), (1540361348425166364749761026925458196465015942003125579303817 : ℤ), (1573073054894952698048364688260125412649479390289113342066533 : ℤ)⟩ ⟨(197 : ℤ), (849127241641808425000428729120872560818409478537203338484065 : ℤ), (917436799920916537924818435089006523112995474824384736320145 : ℤ)⟩ = ⟨(195 : ℤ), (982462484623035288624987695742947238437110340635863624272924 : ℤ), (1015895727427705483505386952902314337102988563850652855113303 : ℤ)⟩ := by
  rfl

theorem ev_A2 : (JA2).value = ⟨(195 : ℤ), (982462484623035288624987695742947238437110340635863624272924 : ℤ), (1015895727427705483505386952902314337102988563850652855113303 : ℤ)⟩ := by
  rw [show (JA2).value = dAdd (JA1).value (JSIQACH).value from rfl, ev_A1, ev_SIQACH]
  exact op_A2

theorem p0_A2 : (JA2).part 0 = ⟨(196 : ℤ), (1257184372083965205615737059252292037300757024672708971499784 : ℤ), (1276281343758105934964403698573148083383507440175705765324658 : ℤ)⟩ := by
  rw [show (JA2).part 0 = dAdd ((JA1).part 0) ((JSIQACH).part 0) from rfl, p0_A1, p0_SIQACH]
  rfl

theorem p1_A2 : (JA2).part 1 = ⟨(196 : ℤ), (1000075865952445074935099700034998546882806521252031671591717 : ℤ), (1006940566079747949516393948201609541457871549699557645474578 : ℤ)⟩ := by
  rw [show (JA2).part 1 = dAdd ((JA1).part 1) ((JSIQACH).part 1) from rfl, p1_A1, p1_SIQACH]
  rfl

theorem p2_A2 : (JA2).part 2 = ⟨(198 : ℤ), (-1338645083339866316304152055976740378476713367221754583465239 : ℤ), (-1307094630264322489861532060983251100096908089715760200851474 : ℤ)⟩ := by
  rw [show (JA2).part 2 = dAdd ((JA1).part 2) ((JSIQACH).part 2) from rfl, p2_A1, p2_SIQACH]
  rfl

def JY4X5 : DCJet := DCJetKit.mul JY4 JX5
theorem JY4X5_mem : JetMem JY4X5 fY4X5 D :=
  DCJetKit.mul_mem (JY4_mem) (JX5_mem)

theorem op_Y4X5 : dMul ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(196 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ := by
  rfl

theorem ev_Y4X5 : (JY4X5).value = ⟨(196 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ := by
  rw [show (JY4X5).value = dMul (JY4).value (JX5).value from rfl, ev_Y4, ev_X5]
  exact op_Y4X5

theorem p0_Y4X5 : (JY4X5).part 0 = ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JY4X5).part 0 = dAdd (dMul (JY4).value ((JX5).part 0)) (dMul (JX5).value ((JY4).part 0)) from rfl, ev_Y4, ev_X5, p0_Y4, p0_X5]
  rfl

theorem p1_Y4X5 : (JY4X5).part 1 = ⟨(196 : ℤ), (1152010722029433501723879472884794417776963375073745076147251 : ℤ), (1176475265123423066506087432269043519770939407388454999234619 : ℤ)⟩ := by
  rw [show (JY4X5).part 1 = dAdd (dMul (JY4).value ((JX5).part 1)) (dMul (JX5).value ((JY4).part 1)) from rfl, ev_Y4, ev_X5, p1_Y4, p1_X5]
  rfl

theorem p2_Y4X5 : (JY4X5).part 2 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4X5).part 2 = dAdd (dMul (JY4).value ((JX5).part 2)) (dMul (JX5).value ((JY4).part 2)) from rfl, ev_Y4, ev_X5, p2_Y4, p2_X5]
  rfl

def JY4X5CH : DCJet := DCJetKit.mul JY4X5 JCH
theorem JY4X5CH_mem : JetMem JY4X5CH fY4X5CH D :=
  DCJetKit.mul_mem (JY4X5_mem) (JCH_mem D)

theorem op_Y4X5CH : dMul ⟨(196 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ := by
  rfl

theorem ev_Y4X5CH : (JY4X5CH).value = ⟨(197 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ := by
  rw [show (JY4X5CH).value = dMul (JY4X5).value (JCH).value from rfl, ev_Y4X5, ev_CH]
  exact op_Y4X5CH

theorem p0_Y4X5CH : (JY4X5CH).part 0 = ⟨(198 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JY4X5CH).part 0 = dAdd (dMul (JY4X5).value ((JCH).part 0)) (dMul (JCH).value ((JY4X5).part 0)) from rfl, ev_Y4X5, ev_CH, p0_Y4X5, p0_CH]
  rfl

theorem p1_Y4X5CH : (JY4X5CH).part 1 = ⟨(197 : ℤ), (1152010722029433501723879472884794417776963375073745076147251 : ℤ), (1176475265123423066506087432269043519770939407388454999234619 : ℤ)⟩ := by
  rw [show (JY4X5CH).part 1 = dAdd (dMul (JY4X5).value ((JCH).part 1)) (dMul (JCH).value ((JY4X5).part 1)) from rfl, ev_Y4X5, ev_CH, p1_Y4X5, p1_CH]
  rfl

theorem p2_Y4X5CH : (JY4X5CH).part 2 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4X5CH).part 2 = dAdd (dMul (JY4X5).value ((JCH).part 2)) (dMul (JCH).value ((JY4X5).part 2)) from rfl, ev_Y4X5, ev_CH, p2_Y4X5, p2_CH]
  rfl

def JA : DCJet := DCJetKit.add JA2 JY4X5CH
theorem JA_mem : JetMem JA fA D :=
  DCJetKit.add_mem (JA2_mem) (JY4X5CH_mem)

theorem op_A : dAdd ⟨(195 : ℤ), (982462484623035288624987695742947238437110340635863624272924 : ℤ), (1015895727427705483505386952902314337102988563850652855113303 : ℤ)⟩ ⟨(197 : ℤ), (1310911460100205599937154926779155415494244087105102873432700 : ℤ), (1367180700905504570844130569210936703029688179514780059040776 : ℤ)⟩ = ⟨(195 : ℤ), (1310190349648086688609276427437736092310671362412139342631099 : ℤ), (1357690902654081626216419595205048512860410608729347869873497 : ℤ)⟩ := by
  rfl

theorem ev_A : (JA).value = ⟨(195 : ℤ), (1310190349648086688609276427437736092310671362412139342631099 : ℤ), (1357690902654081626216419595205048512860410608729347869873497 : ℤ)⟩ := by
  rw [show (JA).value = dAdd (JA2).value (JY4X5CH).value from rfl, ev_A2, ev_Y4X5CH]
  exact op_A

theorem p0_A : (JA).part 0 = ⟨(196 : ℤ), (1517285852262577427825490020914822873708345137193562716228494 : ℤ), (1547547355842464700696122944127260804142964074186027327240942 : ℤ)⟩ := by
  rw [show (JA).part 0 = dAdd ((JA2).part 0) ((JY4X5CH).part 0) from rfl, p0_A2, p0_Y4X5CH]
  rfl

theorem p1_A : (JA).part 1 = ⟨(196 : ℤ), (1576081226967161825797039436477395755771288208788904209665342 : ℤ), (1595178198641459482769437664336131301343341253393785145091888 : ℤ)⟩ := by
  rw [show (JA).part 1 = dAdd ((JA2).part 1) ((JY4X5CH).part 1) from rfl, p1_A2, p1_Y4X5CH]
  rfl

theorem p2_A : (JA).part 2 = ⟨(198 : ℤ), (-1338645083339866316304152055976740378476713367221754583465239 : ℤ), (-1307094630264322489861532060983251100096908089715760200851474 : ℤ)⟩ := by
  rw [show (JA).part 2 = dAdd ((JA2).part 2) ((JY4X5CH).part 2) from rfl, p2_A2, p2_Y4X5CH]
  rfl

def JSIY6 : DCJet := DCJetKit.mul JSI JY6
theorem JSIY6_mem : JetMem JSIY6 fSIY6 D :=
  DCJetKit.mul_mem (JSI_mem D) (JY6_mem)

theorem op_SIY6 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465238 : ℤ)⟩ := by
  rfl

theorem ev_SIY6 : (JSIY6).value = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465238 : ℤ)⟩ := by
  rw [show (JSIY6).value = dMul (JSI).value (JY6).value from rfl, ev_SI, ev_Y6]
  exact op_SIY6

theorem p0_SIY6 : (JSIY6).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY6).part 0 = dAdd (dMul (JSI).value ((JY6).part 0)) (dMul (JY6).value ((JSI).part 0)) from rfl, ev_SI, ev_Y6, p0_SI, p0_Y6]
  rfl

theorem p1_SIY6 : (JSIY6).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY6).part 1 = dAdd (dMul (JSI).value ((JY6).part 1)) (dMul (JY6).value ((JSI).part 1)) from rfl, ev_SI, ev_Y6, p1_SI, p1_Y6]
  rfl

theorem p2_SIY6 : (JSIY6).part 2 = ⟨(199 : ℤ), (1136276788042180457691927808607832267993707273715849875161088 : ℤ), (1136276788042180458388826096061914241166698469736111172222976 : ℤ)⟩ := by
  rw [show (JSIY6).part 2 = dAdd (dMul (JSI).value ((JY6).part 2)) (dMul (JY6).value ((JSI).part 2)) from rfl, ev_SI, ev_Y6, p2_SI, p2_Y6]
  rfl

def JSIY6Y5 : DCJet := DCJetKit.mul JSIY6 JY5
theorem JSIY6Y5_mem : JetMem JSIY6Y5 fSIY6Y5 D :=
  DCJetKit.mul_mem (JSIY6_mem) (JY5_mem)

theorem op_SIY6Y5 : dMul ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465238 : ℤ)⟩ ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ = ⟨(197 : ℤ), (1487386616706474009838756577382318958349413231442405773959722 : ℤ), (1555638080595178843520099090341992991967911688523950887996097 : ℤ)⟩ := by
  rfl

theorem ev_SIY6Y5 : (JSIY6Y5).value = ⟨(197 : ℤ), (1487386616706474009838756577382318958349413231442405773959722 : ℤ), (1555638080595178843520099090341992991967911688523950887996097 : ℤ)⟩ := by
  rw [show (JSIY6Y5).value = dMul (JSIY6).value (JY5).value from rfl, ev_SIY6, ev_Y5]
  exact op_SIY6Y5

theorem p0_SIY6Y5 : (JSIY6Y5).part 0 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY6Y5).part 0 = dAdd (dMul (JSIY6).value ((JY5).part 0)) (dMul (JY5).value ((JSIY6).part 0)) from rfl, ev_SIY6, ev_Y5, p0_SIY6, p0_Y5]
  rfl

theorem p1_SIY6Y5 : (JSIY6Y5).part 1 = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465238 : ℤ)⟩ := by
  rw [show (JSIY6Y5).part 1 = dAdd (dMul (JSIY6).value ((JY5).part 1)) (dMul (JY5).value ((JSIY6).part 1)) from rfl, ev_SIY6, ev_Y5, p1_SIY6, p1_Y5]
  rfl

theorem p2_SIY6Y5 : (JSIY6Y5).part 2 = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968852 : ℤ)⟩ := by
  rw [show (JSIY6Y5).part 2 = dAdd (dMul (JSIY6).value ((JY5).part 2)) (dMul (JY5).value ((JSIY6).part 2)) from rfl, ev_SIY6, ev_Y5, p2_SIY6, p2_Y5]
  rfl

def JY6X5 : DCJet := DCJetKit.mul JY6 JX5
theorem JY6X5_mem : JetMem JY6X5 fY6X5 D :=
  DCJetKit.mul_mem (JY6_mem) (JX5_mem)

theorem op_Y6X5 : dMul ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(196 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rfl

theorem ev_Y6X5 : (JY6X5).value = ⟨(196 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rw [show (JY6X5).value = dMul (JY6).value (JX5).value from rfl, ev_Y6, ev_X5]
  exact op_Y6X5

theorem p0_Y6X5 : (JY6X5).part 0 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6X5).part 0 = dAdd (dMul (JY6).value ((JX5).part 0)) (dMul (JX5).value ((JY6).part 0)) from rfl, ev_Y6, ev_X5, p0_Y6, p0_X5]
  rfl

theorem p1_Y6X5 : (JY6X5).part 1 = ⟨(196 : ℤ), (1051741162919263950481497814253170034490693228717633547081052 : ℤ), (1100002235860875908651666401060125123740327778257166779588667 : ℤ)⟩ := by
  rw [show (JY6X5).part 1 = dAdd (dMul (JY6).value ((JX5).part 1)) (dMul (JX5).value ((JY6).part 1)) from rfl, ev_Y6, ev_X5, p1_Y6, p1_X5]
  rfl

theorem p2_Y6X5 : (JY6X5).part 2 = ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JY6X5).part 2 = dAdd (dMul (JY6).value ((JX5).part 2)) (dMul (JX5).value ((JY6).part 2)) from rfl, ev_Y6, ev_X5, p2_Y6, p2_X5]
  rfl

def JY6X5CH : DCJet := DCJetKit.mul JY6X5 JCH
theorem JY6X5CH_mem : JetMem JY6X5CH fY6X5CH D :=
  DCJetKit.mul_mem (JY6X5_mem) (JCH_mem D)

theorem op_Y6X5CH : dMul ⟨(196 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rfl

theorem ev_Y6X5CH : (JY6X5CH).value = ⟨(197 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rw [show (JY6X5CH).value = dMul (JY6X5).value (JCH).value from rfl, ev_Y6X5, ev_CH]
  exact op_Y6X5CH

theorem p0_Y6X5CH : (JY6X5CH).part 0 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6X5CH).part 0 = dAdd (dMul (JY6X5).value ((JCH).part 0)) (dMul (JCH).value ((JY6X5).part 0)) from rfl, ev_Y6X5, ev_CH, p0_Y6X5, p0_CH]
  rfl

theorem p1_Y6X5CH : (JY6X5CH).part 1 = ⟨(197 : ℤ), (1051741162919263950481497814253170034490693228717633547081052 : ℤ), (1100002235860875908651666401060125123740327778257166779588667 : ℤ)⟩ := by
  rw [show (JY6X5CH).part 1 = dAdd (dMul (JY6X5).value ((JCH).part 1)) (dMul (JCH).value ((JY6X5).part 1)) from rfl, ev_Y6X5, ev_CH, p1_Y6X5, p1_CH]
  rfl

theorem p2_Y6X5CH : (JY6X5CH).part 2 = ⟨(198 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JY6X5CH).part 2 = dAdd (dMul (JY6X5).value ((JCH).part 2)) (dMul (JCH).value ((JY6X5).part 2)) from rfl, ev_Y6X5, ev_CH, p2_Y6X5, p2_CH]
  rfl

def JB1 : DCJet := DCJetKit.add JSIY6Y5 JY6X5CH
theorem JB1_mem : JetMem JB1 fB1 D :=
  DCJetKit.add_mem (JSIY6Y5_mem) (JY6X5CH_mem)

theorem op_B1 : dAdd ⟨(197 : ℤ), (1487386616706474009838756577382318958349413231442405773959722 : ℤ), (1555638080595178843520099090341992991967911688523950887996097 : ℤ)⟩ ⟨(197 : ℤ), (1196811381322155933722889081010975019980752537494381738826068 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ = ⟨(196 : ℤ), (1342098999014314971780822829196646989165082884468393756392895 : ℤ), (1416974776251001650151293005826383892631977652896103488576574 : ℤ)⟩ := by
  rfl

theorem ev_B1 : (JB1).value = ⟨(196 : ℤ), (1342098999014314971780822829196646989165082884468393756392895 : ℤ), (1416974776251001650151293005826383892631977652896103488576574 : ℤ)⟩ := by
  rw [show (JB1).value = dAdd (JSIY6Y5).value (JY6X5CH).value from rfl, ev_SIY6Y5, ev_Y6X5CH]
  exact op_B1

theorem p0_B1 : (JB1).part 0 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JB1).part 0 = dAdd ((JSIY6Y5).part 0) ((JY6X5CH).part 0) from rfl, p0_SIY6Y5, p0_Y6X5CH]
  rfl

theorem p1_B1 : (JB1).part 1 = ⟨(196 : ℤ), (852644239025712597706131922372397792269573636787756823753394 : ℤ), (884662388765404533401871214524247656489342230934022035660643 : ℤ)⟩ := by
  rw [show (JB1).part 1 = dAdd ((JSIY6Y5).part 1) ((JY6X5CH).part 1) from rfl, p1_SIY6Y5, p1_Y6X5CH]
  rfl

theorem p2_B1 : (JB1).part 2 = ⟨(197 : ℤ), (1166706606029147665581186049521917000803691316872394934958255 : ℤ), (1202765070094756511836283597073617264646818147723326366816994 : ℤ)⟩ := by
  rw [show (JB1).part 2 = dAdd ((JSIY6Y5).part 2) ((JY6X5CH).part 2) from rfl, p2_SIY6Y5, p2_Y6X5CH]
  rfl

def JX6X5 : DCJet := DCJetKit.add JX6 JX5
theorem JX6X5_mem : JetMem JX6X5 fX6X5 D :=
  DCJetKit.add_mem (JX6_mem) (JX5_mem)

theorem op_X6X5 : dAdd ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(196 : ℤ), (1051802911758483160153401485770379513539190266605635989460710 : ℤ), (1100105063637184320795002804810504001454255956315062579175948 : ℤ)⟩ := by
  rfl

theorem ev_X6X5 : (JX6X5).value = ⟨(196 : ℤ), (1051802911758483160153401485770379513539190266605635989460710 : ℤ), (1100105063637184320795002804810504001454255956315062579175948 : ℤ)⟩ := by
  rw [show (JX6X5).value = dAdd (JX6).value (JX5).value from rfl, ev_X6, ev_X5]
  exact op_X6X5

theorem p0_X6X5 : (JX6X5).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX6X5).part 0 = dAdd ((JX6).part 0) ((JX5).part 0) from rfl, p0_X6, p0_X5]
  rfl

theorem p1_X6X5 : (JX6X5).part 1 = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JX6X5).part 1 = dAdd ((JX6).part 1) ((JX5).part 1) from rfl, p1_X6, p1_X5]
  rfl

theorem p2_X6X5 : (JX6X5).part 2 = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JX6X5).part 2 = dAdd ((JX6).part 2) ((JX5).part 2) from rfl, p2_X6, p2_X5]
  rfl

def JQB : DCJet := DCJetKit.sub JX6X5 JX4
theorem JQB_mem : JetMem JQB fQB D :=
  DCJetKit.sub_mem (JX6X5_mem) (JX4_mem)

theorem op_QB : dAdd ⟨(196 : ℤ), (1051802911758483160153401485770379513539190266605635989460710 : ℤ), (1100105063637184320795002804810504001454255956315062579175948 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩) = ⟨(197 : ℤ), (828018403983552129086667108488826155239045280338954459852503 : ℤ), (924622707741582160864796100720593129026387176165344205689665 : ℤ)⟩ := by
  rfl

theorem ev_QB : (JQB).value = ⟨(197 : ℤ), (828018403983552129086667108488826155239045280338954459852503 : ℤ), (924622707741582160864796100720593129026387176165344205689665 : ℤ)⟩ := by
  rw [show (JQB).value = dAdd (JX6X5).value (dNeg (JX4).value) from rfl, ev_X6X5, ev_X4]
  exact op_QB

theorem p0_QB : (JQB).part 0 = ⟨(197 : ℤ), (-1012370967883412965057676704257544199132921689698176452925934 : ℤ), (-1012370967883163873591436118174932439588987886083159486239866 : ℤ)⟩ := by
  rw [show (JQB).part 0 = dAdd ((JX6X5).part 0) (dNeg ((JX4).part 0)) from rfl, p0_X6X5, p0_X4]
  rfl

theorem p1_QB : (JQB).part 1 = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JQB).part 1 = dAdd ((JX6X5).part 1) (dNeg ((JX4).part 1)) from rfl, p1_X6X5, p1_X4]
  rfl

theorem p2_QB : (JQB).part 2 = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JQB).part 2 = dAdd ((JX6X5).part 2) (dNeg ((JX4).part 2)) from rfl, p2_X6X5, p2_X4]
  rfl

def JSIQB : DCJet := DCJetKit.mul JSI JQB
theorem JSIQB_mem : JetMem JSIQB fSIQB D :=
  DCJetKit.mul_mem (JSI_mem D) (JQB_mem)

theorem op_SIQB : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (828018403983552129086667108488826155239045280338954459852503 : ℤ), (924622707741582160864796100720593129026387176165344205689665 : ℤ)⟩ = ⟨(197 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ := by
  rfl

theorem ev_SIQB : (JSIQB).value = ⟨(197 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ := by
  rw [show (JSIQB).value = dMul (JSI).value (JQB).value from rfl, ev_SI, ev_QB]
  exact op_SIQB

theorem p0_SIQB : (JSIQB).part 0 = ⟨(197 : ℤ), (-1431708752933499646099749717823721647736341186520546576860539 : ℤ), (-1431708752933147376691829038845868657672071164881970842702969 : ℤ)⟩ := by
  rw [show (JSIQB).part 0 = dAdd (dMul (JSI).value ((JQB).part 0)) (dMul (JQB).value ((JSI).part 0)) from rfl, ev_SI, ev_QB, p0_SI, p0_QB]
  rfl

theorem p1_SIQB : (JSIQB).part 1 = ⟨(197 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968853 : ℤ)⟩ := by
  rw [show (JSIQB).part 1 = dAdd (dMul (JSI).value ((JQB).part 1)) (dMul (JQB).value ((JSI).part 1)) from rfl, ev_SI, ev_QB, p1_SI, p1_QB]
  rfl

theorem p2_SIQB : (JSIQB).part 2 = ⟨(197 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465239 : ℤ)⟩ := by
  rw [show (JSIQB).part 2 = dAdd (dMul (JSI).value ((JQB).part 2)) (dMul (JQB).value ((JSI).part 2)) from rfl, ev_SI, ev_QB, p2_SI, p2_QB]
  rfl

def JSIQBCH : DCJet := DCJetKit.mul JSIQB JCH
theorem JSIQBCH_mem : JetMem JSIQBCH fSIQBCH D :=
  DCJetKit.mul_mem (JSIQB_mem) (JCH_mem D)

theorem op_SIQBCH : dMul ⟨(197 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(198 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ := by
  rfl

theorem ev_SIQBCH : (JSIQBCH).value = ⟨(198 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ := by
  rw [show (JSIQBCH).value = dMul (JSIQB).value (JCH).value from rfl, ev_SIQB, ev_CH]
  exact op_SIQBCH

theorem p0_SIQBCH : (JSIQBCH).part 0 = ⟨(198 : ℤ), (-1431708752933499646099749717823721647736341186520546576860539 : ℤ), (-1431708752933147376691829038845868657672071164881970842702969 : ℤ)⟩ := by
  rw [show (JSIQBCH).part 0 = dAdd (dMul (JSIQB).value ((JCH).part 0)) (dMul (JCH).value ((JSIQB).part 0)) from rfl, ev_SIQB, ev_CH, p0_SIQB, p0_CH]
  rfl

theorem p1_SIQBCH : (JSIQBCH).part 1 = ⟨(198 : ℤ), (1293007291343846442323360252393710655977030183661374891001668 : ℤ), (1320466091852077960745690211930783646255809759405366485968853 : ℤ)⟩ := by
  rw [show (JSIQBCH).part 1 = dAdd (dMul (JSIQB).value ((JCH).part 1)) (dMul (JCH).value ((JSIQB).part 1)) from rfl, ev_SIQB, ev_CH, p1_SIQB, p1_CH]
  rfl

theorem p2_SIQBCH : (JSIQBCH).part 2 = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465239 : ℤ)⟩ := by
  rw [show (JSIQBCH).part 2 = dAdd (dMul (JSIQB).value ((JCH).part 2)) (dMul (JCH).value ((JSIQB).part 2)) from rfl, ev_SIQB, ev_CH, p2_SIQB, p2_CH]
  rfl

def JB2 : DCJet := DCJetKit.add JB1 JSIQBCH
theorem JB2_mem : JetMem JB2 fB2 D :=
  DCJetKit.add_mem (JB1_mem) (JSIQBCH_mem)

theorem op_B2 : dAdd ⟨(196 : ℤ), (1342098999014314971780822829196646989165082884468393756392895 : ℤ), (1416974776251001650151293005826383892631977652896103488576574 : ℤ)⟩ ⟨(198 : ℤ), (1170994856808063812340800911247027686358725636114015925837779 : ℤ), (1307613973366280037866202837520135482629869880995689454581885 : ℤ)⟩ = ⟨(195 : ℤ), (817423856608165462433011528504201955377382146748448868926169 : ℤ), (871939134796285829808921857603208881644722561572512926111023 : ℤ)⟩ := by
  rfl

theorem ev_B2 : (JB2).value = ⟨(195 : ℤ), (817423856608165462433011528504201955377382146748448868926169 : ℤ), (871939134796285829808921857603208881644722561572512926111023 : ℤ)⟩ := by
  rw [show (JB2).value = dAdd (JB1).value (JSIQBCH).value from rfl, ev_B1, ev_SIQBCH]
  exact op_B2

theorem p0_B2 : (JB2).part 0 = ⟨(198 : ℤ), (-1431708752933499646099749717823721647736341186520546576860539 : ℤ), (-1431708752933147376691829038845868657672071164881970842702969 : ℤ)⟩ := by
  rw [show (JB2).part 0 = dAdd ((JB1).part 0) ((JSIQBCH).part 0) from rfl, p0_B1, p0_SIQBCH]
  rfl

theorem p1_B2 : (JB2).part 1 = ⟨(196 : ℤ), (1175896061861674208286971985470825456263831182703100546503811 : ℤ), (1214778911728424023588293767506943568053294670785363657152857 : ℤ)⟩ := by
  rw [show (JB2).part 1 = dAdd ((JB1).part 1) ((JSIQBCH).part 1) from rfl, p1_B1, p1_SIQBCH]
  rfl

theorem p2_B2 : (JB2).part 2 = ⟨(196 : ℤ), (910126960580654455255976040006771275426072680865137517691996 : ℤ), (936043805882344834994179812530993726942587415667101829274807 : ℤ)⟩ := by
  rw [show (JB2).part 2 = dAdd ((JB1).part 2) ((JSIQBCH).part 2) from rfl, p2_B1, p2_SIQBCH]
  rfl

def JY5X6 : DCJet := DCJetKit.mul JY5 JX6
theorem JY5X6_mem : JetMem JY5X6 fY5X6 D :=
  DCJetKit.mul_mem (JY5_mem) (JX6_mem)

theorem op_Y5X6 : dMul ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(196 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rfl

theorem ev_Y5X6 : (JY5X6).value = ⟨(196 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rw [show (JY5X6).value = dMul (JY5).value (JX6).value from rfl, ev_Y5, ev_X6]
  exact op_Y5X6

theorem p0_Y5X6 : (JY5X6).part 0 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5X6).part 0 = dAdd (dMul (JY5).value ((JX6).part 0)) (dMul (JX6).value ((JY5).part 0)) from rfl, ev_Y5, ev_X6, p0_Y5, p0_X6]
  rfl

theorem p1_Y5X6 : (JY5X6).part 1 = ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JY5X6).part 1 = dAdd (dMul (JY5).value ((JX6).part 1)) (dMul (JX6).value ((JY5).part 1)) from rfl, ev_Y5, ev_X6, p1_Y5, p1_X6]
  rfl

theorem p2_Y5X6 : (JY5X6).part 2 = ⟨(196 : ℤ), (1051741162919263950481497814253170034490693228717633547081052 : ℤ), (1100002235860875908651666401060125123740327778257166779588667 : ℤ)⟩ := by
  rw [show (JY5X6).part 2 = dAdd (dMul (JY5).value ((JX6).part 2)) (dMul (JX6).value ((JY5).part 2)) from rfl, ev_Y5, ev_X6, p2_Y5, p2_X6]
  rfl

def JY5X6CH : DCJet := DCJetKit.mul JY5X6 JCH
theorem JY5X6CH_mem : JetMem JY5X6CH fY5X6CH D :=
  DCJetKit.mul_mem (JY5X6_mem) (JCH_mem D)

theorem op_Y5X6CH : dMul ⟨(196 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rfl

theorem ev_Y5X6CH : (JY5X6CH).value = ⟨(197 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rw [show (JY5X6CH).value = dMul (JY5X6).value (JCH).value from rfl, ev_Y5X6, ev_CH]
  exact op_Y5X6CH

theorem p0_Y5X6CH : (JY5X6CH).part 0 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5X6CH).part 0 = dAdd (dMul (JY5X6).value ((JCH).part 0)) (dMul (JCH).value ((JY5X6).part 0)) from rfl, ev_Y5X6, ev_CH, p0_Y5X6, p0_CH]
  rfl

theorem p1_Y5X6CH : (JY5X6CH).part 1 = ⟨(198 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JY5X6CH).part 1 = dAdd (dMul (JY5X6).value ((JCH).part 1)) (dMul (JCH).value ((JY5X6).part 1)) from rfl, ev_Y5X6, ev_CH, p1_Y5X6, p1_CH]
  rfl

theorem p2_Y5X6CH : (JY5X6CH).part 2 = ⟨(197 : ℤ), (1051741162919263950481497814253170034490693228717633547081052 : ℤ), (1100002235860875908651666401060125123740327778257166779588667 : ℤ)⟩ := by
  rw [show (JY5X6CH).part 2 = dAdd (dMul (JY5X6).value ((JCH).part 2)) (dMul (JCH).value ((JY5X6).part 2)) from rfl, ev_Y5X6, ev_CH, p2_Y5X6, p2_CH]
  rfl

def JB : DCJet := DCJetKit.add JB2 JY5X6CH
theorem JB_mem : JetMem JB fB D :=
  DCJetKit.add_mem (JB2_mem) (JY5X6CH_mem)

theorem op_B : dAdd ⟨(195 : ℤ), (817423856608165462433011528504201955377382146748448868926169 : ℤ), (871939134796285829808921857603208881644722561572512926111023 : ℤ)⟩ ⟨(197 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ = ⟨(195 : ℤ), (1119886522603568120731881860118615247481823501238675430013657 : ℤ), (1195916663905892051976153956058604262341990085187101712960850 : ℤ)⟩ := by
  rfl

theorem ev_B : (JB).value = ⟨(195 : ℤ), (1119886522603568120731881860118615247481823501238675430013657 : ℤ), (1195916663905892051976153956058604262341990085187101712960850 : ℤ)⟩ := by
  rw [show (JB).value = dAdd (JB2).value (JY5X6CH).value from rfl, ev_B2, ev_Y5X6CH]
  exact op_B

theorem p0_B : (JB).part 0 = ⟨(198 : ℤ), (-1431708752933499646099749717823721647736341186520546576860539 : ℤ), (-1431708752933147376691829038845868657672071164881970842702969 : ℤ)⟩ := by
  rw [show (JB).part 0 = dAdd ((JB2).part 0) ((JY5X6CH).part 0) from rfl, p0_B2, p0_Y5X6CH]
  rfl

theorem p1_B : (JB).part 1 = ⟨(196 : ℤ), (1441696037562303566153919766693484376625838203485064796505455 : ℤ), (1493565431462657418254075924358082848020966014932573384824547 : ℤ)⟩ := by
  rw [show (JB).part 1 = dAdd ((JB2).part 1) ((JY5X6CH).part 1) from rfl, p1_B2, p1_Y5X6CH]
  rfl

theorem p2_B : (JB).part 2 = ⟨(196 : ℤ), (1435997542040286430496724947133356292671419295223954291232522 : ℤ), (1486044923812782789320013013061056288812751304795685219069141 : ℤ)⟩ := by
  rw [show (JB).part 2 = dAdd ((JB2).part 2) ((JY5X6CH).part 2) from rfl, p2_B2, p2_Y5X6CH]
  rfl

def JSIY4 : DCJet := DCJetKit.mul JSI JY4
theorem JSIY4_mem : JetMem JSIY4 fSIY4 D :=
  DCJetKit.mul_mem (JSI_mem D) (JY4_mem)

theorem op_SIY4 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702970 : ℤ), (1431708752933499646099749717823721647736341186520546576860538 : ℤ)⟩ := by
  rfl

theorem ev_SIY4 : (JSIY4).value = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702970 : ℤ), (1431708752933499646099749717823721647736341186520546576860538 : ℤ)⟩ := by
  rw [show (JSIY4).value = dMul (JSI).value (JY4).value from rfl, ev_SI, ev_Y4]
  exact op_SIY4

theorem p0_SIY4 : (JSIY4).part 0 = ⟨(199 : ℤ), (1136276788042180457691927808607832267993707273715849875161088 : ℤ), (1136276788042180458388826096061914241166698469736111172222976 : ℤ)⟩ := by
  rw [show (JSIY4).part 0 = dAdd (dMul (JSI).value ((JY4).part 0)) (dMul (JY4).value ((JSI).part 0)) from rfl, ev_SI, ev_Y4, p0_SI, p0_Y4]
  rfl

theorem p1_SIY4 : (JSIY4).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY4).part 1 = dAdd (dMul (JSI).value ((JY4).part 1)) (dMul (JY4).value ((JSI).part 1)) from rfl, ev_SI, ev_Y4, p1_SI, p1_Y4]
  rfl

theorem p2_SIY4 : (JSIY4).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY4).part 2 = dAdd (dMul (JSI).value ((JY4).part 2)) (dMul (JY4).value ((JSI).part 2)) from rfl, ev_SI, ev_Y4, p2_SI, p2_Y4]
  rfl

def JSIY4Y6 : DCJet := DCJetKit.mul JSIY4 JY6
theorem JSIY4Y6_mem : JetMem JSIY4Y6 fSIY4Y6 D :=
  DCJetKit.mul_mem (JSIY4_mem) (JY6_mem)

theorem op_SIY4Y6 : dMul ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702970 : ℤ), (1431708752933499646099749717823721647736341186520546576860538 : ℤ)⟩ ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ = ⟨(196 : ℤ), (823469617066523168612765198419448193061052096520928926536428 : ℤ), (843346402504323282645984307943036745050526375875773062922154 : ℤ)⟩ := by
  rfl

theorem ev_SIY4Y6 : (JSIY4Y6).value = ⟨(196 : ℤ), (823469617066523168612765198419448193061052096520928926536428 : ℤ), (843346402504323282645984307943036745050526375875773062922154 : ℤ)⟩ := by
  rw [show (JSIY4Y6).value = dMul (JSIY4).value (JY6).value from rfl, ev_SIY4, ev_Y6]
  exact op_SIY4Y6

theorem p0_SIY4Y6 : (JSIY4Y6).part 0 = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465238 : ℤ)⟩ := by
  rw [show (JSIY4Y6).part 0 = dAdd (dMul (JSIY4).value ((JY6).part 0)) (dMul (JY6).value ((JSIY4).part 0)) from rfl, ev_SIY4, ev_Y6, p0_SIY4, p0_Y6]
  rfl

theorem p1_SIY4Y6 : (JSIY4Y6).part 1 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JSIY4Y6).part 1 = dAdd (dMul (JSIY4).value ((JY6).part 1)) (dMul (JY6).value ((JSIY4).part 1)) from rfl, ev_SIY4, ev_Y6, p1_SIY4, p1_Y6]
  rfl

theorem p2_SIY4Y6 : (JSIY4Y6).part 2 = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702970 : ℤ), (1431708752933499646099749717823721647736341186520546576860538 : ℤ)⟩ := by
  rw [show (JSIY4Y6).part 2 = dAdd (dMul (JSIY4).value ((JY6).part 2)) (dMul (JY6).value ((JSIY4).part 2)) from rfl, ev_SIY4, ev_Y6, p2_SIY4, p2_Y6]
  rfl

def JY4X6 : DCJet := DCJetKit.mul JY4 JX6
theorem JY4X6_mem : JetMem JY4X6 fY4X6 D :=
  DCJetKit.mul_mem (JY4_mem) (JX6_mem)

theorem op_Y4X6 : dMul ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(196 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ := by
  rfl

theorem ev_Y4X6 : (JY4X6).value = ⟨(196 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ := by
  rw [show (JY4X6).value = dMul (JY4).value (JX6).value from rfl, ev_Y4, ev_X6]
  exact op_Y4X6

theorem p0_Y4X6 : (JY4X6).part 0 = ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JY4X6).part 0 = dAdd (dMul (JY4).value ((JX6).part 0)) (dMul (JX6).value ((JY4).part 0)) from rfl, ev_Y4, ev_X6, p0_Y4, p0_X6]
  rfl

theorem p1_Y4X6 : (JY4X6).part 1 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4X6).part 1 = dAdd (dMul (JY4).value ((JX6).part 1)) (dMul (JX6).value ((JY4).part 1)) from rfl, ev_Y4, ev_X6, p1_Y4, p1_X6]
  rfl

theorem p2_Y4X6 : (JY4X6).part 2 = ⟨(196 : ℤ), (1164561900657656158593860711276346716786778601093393011237315 : ℤ), (1192671920200173116815609547091292453827400507337720956100075 : ℤ)⟩ := by
  rw [show (JY4X6).part 2 = dAdd (dMul (JY4).value ((JX6).part 2)) (dMul (JX6).value ((JY4).part 2)) from rfl, ev_Y4, ev_X6, p2_Y4, p2_X6]
  rfl

def JY4X6CH : DCJet := DCJetKit.mul JY4X6 JCH
theorem JY4X6CH_mem : JetMem JY4X6CH fY4X6CH D :=
  DCJetKit.mul_mem (JY4X6_mem) (JCH_mem D)

theorem op_Y4X6CH : dMul ⟨(196 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ := by
  rfl

theorem ev_Y4X6CH : (JY4X6CH).value = ⟨(197 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ := by
  rw [show (JY4X6CH).value = dMul (JY4X6).value (JCH).value from rfl, ev_Y4X6, ev_CH]
  exact op_Y4X6CH

theorem p0_Y4X6CH : (JY4X6CH).part 0 = ⟨(198 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JY4X6CH).part 0 = dAdd (dMul (JY4X6).value ((JCH).part 0)) (dMul (JCH).value ((JY4X6).part 0)) from rfl, ev_Y4X6, ev_CH, p0_Y4X6, p0_CH]
  rfl

theorem p1_Y4X6CH : (JY4X6CH).part 1 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4X6CH).part 1 = dAdd (dMul (JY4X6).value ((JCH).part 1)) (dMul (JCH).value ((JY4X6).part 1)) from rfl, ev_Y4X6, ev_CH, p1_Y4X6, p1_CH]
  rfl

theorem p2_Y4X6CH : (JY4X6CH).part 2 = ⟨(197 : ℤ), (1164561900657656158593860711276346716786778601093393011237315 : ℤ), (1192671920200173116815609547091292453827400507337720956100075 : ℤ)⟩ := by
  rw [show (JY4X6CH).part 2 = dAdd (dMul (JY4X6).value ((JCH).part 2)) (dMul (JCH).value ((JY4X6).part 2)) from rfl, ev_Y4X6, ev_CH, p2_Y4X6, p2_CH]
  rfl

def JC1 : DCJet := DCJetKit.add JSIY4Y6 JY4X6CH
theorem JC1_mem : JetMem JC1 fC1 D :=
  DCJetKit.add_mem (JSIY4Y6_mem) (JY4X6CH_mem)

theorem op_C1 : dAdd ⟨(196 : ℤ), (823469617066523168612765198419448193061052096520928926536428 : ℤ), (843346402504323282645984307943036745050526375875773062922154 : ℤ)⟩ ⟨(197 : ℤ), (1339631877531171963649416817362200958624515384741099820008289 : ℤ), (1405084059460882026702934098677799114174131535300239337345768 : ℤ)⟩ = ⟨(196 : ℤ), (1493285555832109150437473607100548672373309788891478836540572 : ℤ), (1545888432234764295997451357281936302137592143525892731595038 : ℤ)⟩ := by
  rfl

theorem ev_C1 : (JC1).value = ⟨(196 : ℤ), (1493285555832109150437473607100548672373309788891478836540572 : ℤ), (1545888432234764295997451357281936302137592143525892731595038 : ℤ)⟩ := by
  rw [show (JC1).value = dAdd (JSIY4Y6).value (JY4X6CH).value from rfl, ev_SIY4Y6, ev_Y4X6CH]
  exact op_C1

theorem p0_C1 : (JC1).part 0 = ⟨(197 : ℤ), (1185147266533419960664661592936943390772468086421808600429026 : ℤ), (1226895581138399947483640341690648749173699371905296747075999 : ℤ)⟩ := by
  rw [show (JC1).part 0 = dAdd ((JSIY4Y6).part 0) ((JY4X6CH).part 0) from rfl, p0_SIY4Y6, p0_Y4X6CH]
  rfl

theorem p1_C1 : (JC1).part 1 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC1).part 1 = dAdd ((JSIY4Y6).part 1) ((JY4X6CH).part 1) from rfl, p1_SIY4Y6, p1_Y4X6CH]
  rfl

theorem p2_C1 : (JC1).part 2 = ⟨(196 : ℤ), (940208138562114923469887615349640522811407091767189216294400 : ℤ), (954263148333461469932742203001576638847785550298997122265172 : ℤ)⟩ := by
  rw [show (JC1).part 2 = dAdd ((JSIY4Y6).part 2) ((JY4X6CH).part 2) from rfl, p2_SIY4Y6, p2_Y4X6CH]
  rfl

def JX4X6add : DCJet := DCJetKit.add JX4 JX6
theorem JX4X6add_mem : JetMem JX4X6add fX4X6add D :=
  DCJetKit.add_mem (JX4_mem) (JX6_mem)

theorem op_X4X6add : dAdd ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(196 : ℤ), (1169393661167651956096500316895525277665076409796318976334405 : ℤ), (1195366749235173884941632245228244995855010314730578214877839 : ℤ)⟩ := by
  rfl

theorem ev_X4X6add : (JX4X6add).value = ⟨(196 : ℤ), (1169393661167651956096500316895525277665076409796318976334405 : ℤ), (1195366749235173884941632245228244995855010314730578214877839 : ℤ)⟩ := by
  rw [show (JX4X6add).value = dAdd (JX4).value (JX6).value from rfl, ev_X4, ev_X6]
  exact op_X4X6add

theorem p0_X4X6add : (JX4X6add).part 0 = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JX4X6add).part 0 = dAdd ((JX4).part 0) ((JX6).part 0) from rfl, p0_X4, p0_X6]
  rfl

theorem p1_X4X6add : (JX4X6add).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JX4X6add).part 1 = dAdd ((JX4).part 1) ((JX6).part 1) from rfl, p1_X4, p1_X6]
  rfl

theorem p2_X4X6add : (JX4X6add).part 2 = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JX4X6add).part 2 = dAdd ((JX4).part 2) ((JX6).part 2) from rfl, p2_X4, p2_X6]
  rfl

def JQC : DCJet := DCJetKit.sub JX4X6add JX5
theorem JQC_mem : JetMem JQC fQC D :=
  DCJetKit.sub_mem (JX4X6add_mem) (JX5_mem)

theorem op_QC : dAdd ⟨(196 : ℤ), (1169393661167651956096500316895525277665076409796318976334405 : ℤ), (1195366749235173884941632245228244995855010314730578214877839 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩) = ⟨(197 : ℤ), (1253723273997868849266123651574599672292326283551351705003674 : ℤ), (1350327577755898881044252643806366646079668179377741450840836 : ℤ)⟩ := by
  rfl

theorem ev_QC : (JQC).value = ⟨(197 : ℤ), (1253723273997868849266123651574599672292326283551351705003674 : ℤ), (1350327577755898881044252643806366646079668179377741450840836 : ℤ)⟩ := by
  rw [show (JQC).value = dAdd (JX4X6add).value (dNeg (JX5).value) from rfl, ev_X4X6add, ev_X5]
  exact op_QC

theorem p0_QC : (JQC).part 0 = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JQC).part 0 = dAdd ((JX4X6add).part 0) (dNeg ((JX5).part 0)) from rfl, p0_X4X6add, p0_X5]
  rfl

theorem p1_QC : (JQC).part 1 = ⟨(197 : ℤ), (-933710527875502855212885292757040016724189579240055687286716 : ℤ), (-914294223832883731526888470543487633156320138947416727100993 : ℤ)⟩ := by
  rw [show (JQC).part 1 = dAdd ((JX4X6add).part 1) (dNeg ((JX5).part 1)) from rfl, p1_X4X6add, p1_X5]
  rfl

theorem p2_QC : (JQC).part 2 = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JQC).part 2 = dAdd ((JX4X6add).part 2) (dNeg ((JX5).part 2)) from rfl, p2_X4X6add, p2_X5]
  rfl

def JSIQC : DCJet := DCJetKit.mul JSI JQC
theorem JSIQC_mem : JetMem JSIQC fSIQC D :=
  DCJetKit.mul_mem (JSI_mem D) (JQC_mem)

theorem op_SIQC : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (1253723273997868849266123651574599672292326283551351705003674 : ℤ), (1350327577755898881044252643806366646079668179377741450840836 : ℤ)⟩ = ⟨(196 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ := by
  rfl

theorem ev_SIQC : (JSIQC).value = ⟨(196 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ := by
  rw [show (JSIQC).value = dMul (JSI).value (JQC).value from rfl, ev_SI, ev_QC]
  exact op_SIQC

theorem p0_SIQC : (JSIQC).part 0 = ⟨(197 : ℤ), (1431708752933147376691829038845868657672071164881970842702969 : ℤ), (1431708752933499646099749717823721647736341186520546576860539 : ℤ)⟩ := by
  rw [show (JSIQC).part 0 = dAdd (dMul (JSI).value ((JQC).part 0)) (dMul (JQC).value ((JSI).part 0)) from rfl, ev_SI, ev_QC, p0_SI, p0_QC]
  rfl

theorem p1_SIQC : (JSIQC).part 1 = ⟨(197 : ℤ), (-1320466091852077960745690211930783646255809759405366485968853 : ℤ), (-1293007291343846442323360252393710655977030183661374891001668 : ℤ)⟩ := by
  rw [show (JSIQC).part 1 = dAdd (dMul (JSI).value ((JQC).part 1)) (dMul (JQC).value ((JSI).part 1)) from rfl, ev_SI, ev_QC, p1_SI, p1_QC]
  rfl

theorem p2_SIQC : (JSIQC).part 2 = ⟨(197 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465239 : ℤ)⟩ := by
  rw [show (JSIQC).part 2 = dAdd (dMul (JSI).value ((JQC).part 2)) (dMul (JQC).value ((JSI).part 2)) from rfl, ev_SI, ev_QC, p2_SI, p2_QC]
  rfl

def JSIQCCH : DCJet := DCJetKit.mul JSIQC JCH
theorem JSIQCCH_mem : JetMem JSIQCCH fSIQCCH D :=
  DCJetKit.mul_mem (JSIQC_mem) (JCH_mem D)

theorem op_SIQCCH : dMul ⟨(196 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ := by
  rfl

theorem ev_SIQCCH : (JSIQCCH).value = ⟨(197 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ := by
  rw [show (JSIQCCH).value = dMul (JSIQC).value (JCH).value from rfl, ev_SIQC, ev_CH]
  exact op_SIQCCH

theorem p0_SIQCCH : (JSIQCCH).part 0 = ⟨(198 : ℤ), (1431708752933147376691829038845868657672071164881970842702969 : ℤ), (1431708752933499646099749717823721647736341186520546576860539 : ℤ)⟩ := by
  rw [show (JSIQCCH).part 0 = dAdd (dMul (JSIQC).value ((JCH).part 0)) (dMul (JCH).value ((JSIQC).part 0)) from rfl, ev_SIQC, ev_CH, p0_SIQC, p0_CH]
  rfl

theorem p1_SIQCCH : (JSIQCCH).part 1 = ⟨(198 : ℤ), (-1320466091852077960745690211930783646255809759405366485968853 : ℤ), (-1293007291343846442323360252393710655977030183661374891001668 : ℤ)⟩ := by
  rw [show (JSIQCCH).part 1 = dAdd (dMul (JSIQC).value ((JCH).part 1)) (dMul (JCH).value ((JSIQC).part 1)) from rfl, ev_SIQC, ev_CH, p1_SIQC, p1_CH]
  rfl

theorem p2_SIQCCH : (JSIQCCH).part 2 = ⟨(198 : ℤ), (1307094630264322489861532060983251100096908089715760200851474 : ℤ), (1338645083339866316304152055976740378476713367221754583465239 : ℤ)⟩ := by
  rw [show (JSIQCCH).part 2 = dAdd (dMul (JSIQC).value ((JCH).part 2)) (dMul (JCH).value ((JSIQC).part 2)) from rfl, ev_SIQC, ev_CH, p2_SIQC, p2_CH]
  rfl

def JC2b : DCJet := DCJetKit.add JC1 JSIQCCH
theorem JC2b_mem : JetMem JC2b fC2b D :=
  DCJetKit.add_mem (JC1_mem) (JSIQCCH_mem)

theorem op_C2b : dAdd ⟨(196 : ℤ), (1493285555832109150437473607100548672373309788891478836540572 : ℤ), (1545888432234764295997451357281936302137592143525892731595038 : ℤ)⟩ ⟨(197 : ℤ), (886516228775293015617150465028376066486873432319080125396948 : ℤ), (954825787054401128564471486127802549056445602178417601649961 : ℤ)⟩ = ⟨(195 : ℤ), (968271835109877829123024419807368352808373252525509449619523 : ℤ), (1011650662880982430139843550172918788332907472307550766210010 : ℤ)⟩ := by
  rfl

theorem ev_C2b : (JC2b).value = ⟨(195 : ℤ), (968271835109877829123024419807368352808373252525509449619523 : ℤ), (1011650662880982430139843550172918788332907472307550766210010 : ℤ)⟩ := by
  rw [show (JC2b).value = dAdd (JC1).value (JSIQCCH).value from rfl, ev_C1, ev_SIQCCH]
  exact op_C2b

theorem p0_C2b : (JC2b).part 0 = ⟨(196 : ℤ), (950500821499996824505288056179938859804251834431397010890255 : ℤ), (971374978802574885266757600301254786520934982582785017753135 : ℤ)⟩ := by
  rw [show (JC2b).part 0 = dAdd ((JC1).part 0) ((JSIQCCH).part 0) from rfl, p0_C1, p0_SIQCCH]
  rfl

theorem p1_C2b : (JC2b).part 1 = ⟨(198 : ℤ), (-1320466091852077960745690211930783646255809759405366485968853 : ℤ), (-1293007291343846442323360252393710655977030183661374891001668 : ℤ)⟩ := by
  rw [show (JC2b).part 1 = dAdd ((JC1).part 1) ((JSIQCCH).part 1) from rfl, p1_C1, p1_SIQCCH]
  rfl

theorem p2_C2b : (JC2b).part 2 = ⟨(196 : ℤ), (1266981796128195545935270630595453297835634114196129266507268 : ℤ), (1288924419168428049008780216995761733466963892104435768131482 : ℤ)⟩ := by
  rw [show (JC2b).part 2 = dAdd ((JC1).part 2) ((JSIQCCH).part 2) from rfl, p2_C1, p2_SIQCCH]
  rfl

def JY6X4 : DCJet := DCJetKit.mul JY6 JX4
theorem JY6X4_mem : JetMem JY6X4 fY6X4 D :=
  DCJetKit.mul_mem (JY6_mem) (JX4_mem)

theorem op_Y6X4 : dMul ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ = ⟨(196 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ := by
  rfl

theorem ev_Y6X4 : (JY6X4).value = ⟨(196 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ := by
  rw [show (JY6X4).value = dMul (JY6).value (JX4).value from rfl, ev_Y6, ev_X4]
  exact op_Y6X4

theorem p0_Y6X4 : (JY6X4).part 0 = ⟨(196 : ℤ), (1164561900657656158593860711276346716786778601093393011237314 : ℤ), (1192671920200173116815609547091292453827400507337720956100076 : ℤ)⟩ := by
  rw [show (JY6X4).part 0 = dAdd (dMul (JY6).value ((JX4).part 0)) (dMul (JX4).value ((JY6).part 0)) from rfl, ev_Y6, ev_X4, p0_Y6, p0_X4]
  rfl

theorem p1_Y6X4 : (JY6X4).part 1 = ⟨(400 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6X4).part 1 = dAdd (dMul (JY6).value ((JX4).part 1)) (dMul (JX4).value ((JY6).part 1)) from rfl, ev_Y6, ev_X4, p1_Y6, p1_X4]
  rfl

theorem p2_Y6X4 : (JY6X4).part 2 = ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JY6X4).part 2 = dAdd (dMul (JY6).value ((JX4).part 2)) (dMul (JX4).value ((JY6).part 2)) from rfl, ev_Y6, ev_X4, p2_Y6, p2_X4]
  rfl

def JY6X4CH : DCJet := DCJetKit.mul JY6X4 JCH
theorem JY6X4CH_mem : JetMem JY6X4CH fY6X4CH D :=
  DCJetKit.mul_mem (JY6X4_mem) (JCH_mem D)

theorem op_Y6X4CH : dMul ⟨(196 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ := by
  rfl

theorem ev_Y6X4CH : (JY6X4CH).value = ⟨(197 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ := by
  rw [show (JY6X4CH).value = dMul (JY6X4).value (JCH).value from rfl, ev_Y6X4, ev_CH]
  exact op_Y6X4CH

theorem p0_Y6X4CH : (JY6X4CH).part 0 = ⟨(197 : ℤ), (1164561900657656158593860711276346716786778601093393011237314 : ℤ), (1192671920200173116815609547091292453827400507337720956100076 : ℤ)⟩ := by
  rw [show (JY6X4CH).part 0 = dAdd (dMul (JY6X4).value ((JCH).part 0)) (dMul (JCH).value ((JY6X4).part 0)) from rfl, ev_Y6X4, ev_CH, p0_Y6X4, p0_CH]
  rfl

theorem p1_Y6X4CH : (JY6X4CH).part 1 = ⟨(600 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6X4CH).part 1 = dAdd (dMul (JY6X4).value ((JCH).part 1)) (dMul (JCH).value ((JY6X4).part 1)) from rfl, ev_Y6X4, ev_CH, p1_Y6X4, p1_CH]
  rfl

theorem p2_Y6X4CH : (JY6X4CH).part 2 = ⟨(198 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JY6X4CH).part 2 = dAdd (dMul (JY6X4).value ((JCH).part 2)) (dMul (JCH).value ((JY6X4).part 2)) from rfl, ev_Y6X4, ev_CH, p2_Y6X4, p2_CH]
  rfl

def JC : DCJet := DCJetKit.add JC2b JY6X4CH
theorem JC_mem : JetMem JC fC D :=
  DCJetKit.add_mem (JC2b_mem) (JY6X4CH_mem)

theorem op_C : dAdd ⟨(195 : ℤ), (968271835109877829123024419807368352808373252525509449619523 : ℤ), (1011650662880982430139843550172918788332907472307550766210010 : ℤ)⟩ ⟨(197 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391380 : ℤ)⟩ = ⟨(195 : ℤ), (1335108833817039519080090543859417568596208511869928248159277 : ℤ), (1387342317744129399973935671924094705106485942740566760057855 : ℤ)⟩ := by
  rfl

theorem ev_C : (JC).value = ⟨(195 : ℤ), (1335108833817039519080090543859417568596208511869928248159277 : ℤ), (1387342317744129399973935671924094705106485942740566760057855 : ℤ)⟩ := by
  rw [show (JC).value = dAdd (JC2b).value (JY6X4CH).value from rfl, ev_C2b, ev_Y6X4CH]
  exact op_C

theorem p0_C : (JC).part 0 = ⟨(196 : ℤ), (1532781771828824903802218411818112218197641134978093516508912 : ℤ), (1567710938902661443674562373846901013434635236251645495803173 : ℤ)⟩ := by
  rw [show (JC).part 0 = dAdd ((JC2b).part 0) ((JY6X4CH).part 0) from rfl, p0_C2b, p0_Y6X4CH]
  rfl

theorem p1_C : (JC).part 1 = ⟨(198 : ℤ), (-1320466091852077960745690211930783646255809759405366485968853 : ℤ), (-1293007291343846442323360252393710655977030183661374891001668 : ℤ)⟩ := by
  rw [show (JC).part 1 = dAdd ((JC2b).part 1) ((JY6X4CH).part 1) from rfl, p1_C2b, p1_Y6X4CH]
  rfl

theorem p2_C : (JC).part 2 = ⟨(195 : ℤ), (792939325505696083058286503910278508153082649156162252336412 : ℤ), (803910637025890798406907091379372475713398852661257573949356 : ℤ)⟩ := by
  rw [show (JC).part 2 = dAdd ((JC2b).part 2) ((JY6X4CH).part 2) from rfl, p2_C2b, p2_Y6X4CH]
  rfl

def JD4A : DCJet := DCJetKit.mul JX5 JQC
theorem JD4A_mem : JetMem JD4A fD4A D :=
  DCJetKit.mul_mem (JX5_mem) (JQC_mem)

theorem op_D4A : dMul ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ ⟨(197 : ℤ), (1253723273997868849266123651574599672292326283551351705003674 : ℤ), (1350327577755898881044252643806366646079668179377741450840836 : ℤ)⟩ = ⟨(194 : ℤ), (811718362051959021221070227209858817434547300696546197227828 : ℤ), (911791162911414164264663553772158721208345175519987873310647 : ℤ)⟩ := by
  rfl

theorem ev_D4A : (JD4A).value = ⟨(194 : ℤ), (811718362051959021221070227209858817434547300696546197227828 : ℤ), (911791162911414164264663553772158721208345175519987873310647 : ℤ)⟩ := by
  rw [show (JD4A).value = dMul (JX5).value (JQC).value from rfl, ev_X5, ev_QC]
  exact op_D4A

theorem p0_D4A : (JD4A).part 0 = ⟨(195 : ℤ), (1310911460100205599937154926779155415494244087105102873432699 : ℤ), (1367180700905504570844130569210936703029688179514780059040777 : ℤ)⟩ := by
  rw [show (JD4A).part 0 = dAdd (dMul (JX5).value ((JQC).part 0)) (dMul (JQC).value ((JX5).part 0)) from rfl, ev_X5, ev_QC, p0_X5, p0_QC]
  rfl

theorem p1_D4A : (JD4A).part 1 = ⟨(195 : ℤ), (165701749143191126376653451440353003054188669493814820956513 : ℤ), (385301664599411229066953666518190300016458635132405783016576 : ℤ)⟩ := by
  rw [show (JD4A).part 1 = dAdd (dMul (JX5).value ((JQC).part 1)) (dMul (JQC).value ((JX5).part 1)) from rfl, ev_X5, ev_QC, p1_X5, p1_QC]
  rfl

theorem p2_D4A : (JD4A).part 2 = ⟨(195 : ℤ), (1196811381322155933722889081010975019980752537494381738826067 : ℤ), (1278311471906824456782486921310774793296043617268256089157050 : ℤ)⟩ := by
  rw [show (JD4A).part 2 = dAdd (dMul (JX5).value ((JQC).part 2)) (dMul (JQC).value ((JX5).part 2)) from rfl, ev_X5, ev_QC, p2_X5, p2_QC]
  rfl

def JD4B : DCJet := DCJetKit.mul JX6 JQA
theorem JD4B_mem : JetMem JD4B fD4B D :=
  DCJetKit.mul_mem (JX6_mem) (JQA_mem)

theorem op_D4B : dMul ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ ⟨(197 : ℤ), (1200847261310301790901092728145981099641791809959357020890312 : ℤ), (1297451565068331822679221720377748073429133705785746766727475 : ℤ)⟩ = ⟨(194 : ℤ), (794517682910748089668306555125200761408368760420833179199617 : ℤ), (900375736678588096163830783243737965166197690220787624436542 : ℤ)⟩ := by
  rfl

theorem ev_D4B : (JD4B).value = ⟨(194 : ℤ), (794517682910748089668306555125200761408368760420833179199617 : ℤ), (900375736678588096163830783243737965166197690220787624436542 : ℤ)⟩ := by
  rw [show (JD4B).value = dMul (JX6).value (JQA).value from rfl, ev_X6, ev_QA]
  exact op_D4B

theorem p0_D4B : (JD4B).part 0 = ⟨(195 : ℤ), (1339631877531171963649416817362200958624515384741099820008288 : ℤ), (1405084059460882026702934098677799114174131535300239337345769 : ℤ)⟩ := by
  rw [show (JD4B).part 0 = dAdd (dMul (JX6).value ((JQA).part 0)) (dMul (JQA).value ((JX6).part 0)) from rfl, ev_X6, ev_QA, p0_X6, p0_QA]
  rfl

theorem p1_D4B : (JD4B).part 1 = ⟨(195 : ℤ), (1209850663981610633195481326457653168417765417960906244349954 : ℤ), (1295910116438424888668928393821581522789070094458355147399308 : ℤ)⟩ := by
  rw [show (JD4B).part 1 = dAdd (dMul (JX6).value ((JQA).part 1)) (dMul (JQA).value ((JX6).part 1)) from rfl, ev_X6, ev_QA, p1_X6, p1_QA]
  rfl

theorem p2_D4B : (JD4B).part 2 = ⟨(195 : ℤ), (67621016340610397078310196296703164832434483578038845934755 : ℤ), (305492709393207355911926720857854278028960383226722355749198 : ℤ)⟩ := by
  rw [show (JD4B).part 2 = dAdd (dMul (JX6).value ((JQA).part 2)) (dMul (JQA).value ((JX6).part 2)) from rfl, ev_X6, ev_QA, p2_X6, p2_QA]
  rfl

def JD4C : DCJet := DCJetKit.mul JX4 JQB
theorem JD4C_mem : JetMem JD4C fD4C D :=
  DCJetKit.mul_mem (JX4_mem) (JQB_mem)

theorem op_D4C : dMul ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(197 : ℤ), (828018403983552129086667108488826155239045280338954459852503 : ℤ), (924622707741582160864796100720593129026387176165344205689665 : ℤ)⟩ = ⟨(195 : ℤ), (1314562018164287360137992701436860404057508287066124100461832 : ℤ), (1467931010811258200449222572531530043333023059084882674361223 : ℤ)⟩ := by
  rfl

theorem ev_D4C : (JD4C).value = ⟨(195 : ℤ), (1314562018164287360137992701436860404057508287066124100461832 : ℤ), (1467931010811258200449222572531530043333023059084882674361223 : ℤ)⟩ := by
  rw [show (JD4C).value = dMul (JX4).value (JQB).value from rfl, ev_X4, ev_QB]
  exact op_D4C

theorem p0_D4C : (JD4C).part 0 = ⟨(195 : ℤ), (-563936959593221655899974379817076529436628725620965085327782 : ℤ), (-442215536856630791492266849005064094431083927695429540633074 : ℤ)⟩ := by
  rw [show (JD4C).part 0 = dAdd (dMul (JX4).value ((JQB).part 0)) (dMul (JQB).value ((JX4).part 0)) from rfl, ev_X4, ev_QB, p0_X4, p0_QB]
  rfl

theorem p1_D4C : (JD4C).part 1 = ⟨(195 : ℤ), (1451533509757086212172088135834840966398973852592918795945535 : ℤ), (1482358834055877794659363728278073052137135702181452685670699 : ℤ)⟩ := by
  rw [show (JD4C).part 1 = dAdd (dMul (JX4).value ((JQB).part 1)) (dMul (JQB).value ((JX4).part 1)) from rfl, ev_X4, ev_QB, p1_X4, p1_QB]
  rfl

theorem p2_D4C : (JD4C).part 2 = ⟨(195 : ℤ), (1467347994828646759828264496208196863151341037377675194159016 : ℤ), (1502766619452587879336368487004703667094313881732063975391381 : ℤ)⟩ := by
  rw [show (JD4C).part 2 = dAdd (dMul (JX4).value ((JQB).part 2)) (dMul (JQB).value ((JX4).part 2)) from rfl, ev_X4, ev_QB, p2_X4, p2_QB]
  rfl

def JKA : DCJet := DCJetKit.mul JC4 JX5
theorem JKA_mem : JetMem JKA fKA D :=
  DCJetKit.mul_mem (JC4_mem D) (JX5_mem)

theorem op_KA : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ = ⟨(195 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rfl

theorem ev_KA : (JKA).value = ⟨(195 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ := by
  rw [show (JKA).value = dMul (JC4).value (JX5).value from rfl, ev_C4, ev_X5]
  exact op_KA

theorem p0_KA : (JKA).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKA).part 0 = dAdd (dMul (JC4).value ((JX5).part 0)) (dMul (JX5).value ((JC4).part 0)) from rfl, ev_C4, ev_X5, p0_C4, p0_X5]
  rfl

theorem p1_KA : (JKA).part 1 = ⟨(195 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JKA).part 1 = dAdd (dMul (JC4).value ((JX5).part 1)) (dMul (JX5).value ((JC4).part 1)) from rfl, ev_C4, ev_X5, p1_C4, p1_X5]
  rfl

theorem p2_KA : (JKA).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKA).part 2 = dAdd (dMul (JC4).value ((JX5).part 2)) (dMul (JX5).value ((JC4).part 2)) from rfl, ev_C4, ev_X5, p2_C4, p2_X5]
  rfl

def JKB : DCJet := DCJetKit.mul JC4 JX6
theorem JKB_mem : JetMem JKB fKB D :=
  DCJetKit.mul_mem (JC4_mem D) (JX6_mem)

theorem op_KB : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ = ⟨(195 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rfl

theorem ev_KB : (JKB).value = ⟨(195 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ := by
  rw [show (JKB).value = dMul (JC4).value (JX6).value from rfl, ev_C4, ev_X6]
  exact op_KB

theorem p0_KB : (JKB).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKB).part 0 = dAdd (dMul (JC4).value ((JX6).part 0)) (dMul (JX6).value ((JC4).part 0)) from rfl, ev_C4, ev_X6, p0_C4, p0_X6]
  rfl

theorem p1_KB : (JKB).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKB).part 1 = dAdd (dMul (JC4).value ((JX6).part 1)) (dMul (JX6).value ((JC4).part 1)) from rfl, ev_C4, ev_X6, p1_C4, p1_X6]
  rfl

theorem p2_KB : (JKB).part 2 = ⟨(195 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JKB).part 2 = dAdd (dMul (JC4).value ((JX6).part 2)) (dMul (JX6).value ((JC4).part 2)) from rfl, ev_C4, ev_X6, p2_C4, p2_X6]
  rfl

def JKC : DCJet := DCJetKit.mul JC4 JX4
theorem JKC_mem : JetMem JKC fKC D :=
  DCJetKit.mul_mem (JC4_mem D) (JX4_mem)

theorem op_KC : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ = ⟨(195 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rfl

theorem ev_KC : (JKC).value = ⟨(195 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ := by
  rw [show (JKC).value = dMul (JC4).value (JX4).value from rfl, ev_C4, ev_X4]
  exact op_KC

theorem p0_KC : (JKC).part 0 = ⟨(195 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JKC).part 0 = dAdd (dMul (JC4).value ((JX4).part 0)) (dMul (JX4).value ((JC4).part 0)) from rfl, ev_C4, ev_X4, p0_C4, p0_X4]
  rfl

theorem p1_KC : (JKC).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKC).part 1 = dAdd (dMul (JC4).value ((JX4).part 1)) (dMul (JX4).value ((JC4).part 1)) from rfl, ev_C4, ev_X4, p1_C4, p1_X4]
  rfl

theorem p2_KC : (JKC).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JKC).part 2 = dAdd (dMul (JC4).value ((JX4).part 2)) (dMul (JX4).value ((JC4).part 2)) from rfl, ev_C4, ev_X4, p2_C4, p2_X4]
  rfl

def JNA : DCJet := DCJetKit.mul JC2 JY5
theorem JNA_mem : JetMem JNA fNA D :=
  DCJetKit.mul_mem (JC2_mem D) (JY5_mem)

theorem op_NA : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rfl

theorem ev_NA : (JNA).value = ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JNA).value = dMul (JC2).value (JY5).value from rfl, ev_C2, ev_Y5]
  exact op_NA

theorem p0_NA : (JNA).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNA).part 0 = dAdd (dMul (JC2).value ((JY5).part 0)) (dMul (JY5).value ((JC2).part 0)) from rfl, ev_C2, ev_Y5, p0_C2, p0_Y5]
  rfl

theorem p1_NA : (JNA).part 1 = ⟨(198 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JNA).part 1 = dAdd (dMul (JC2).value ((JY5).part 1)) (dMul (JY5).value ((JC2).part 1)) from rfl, ev_C2, ev_Y5, p1_C2, p1_Y5]
  rfl

theorem p2_NA : (JNA).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNA).part 2 = dAdd (dMul (JC2).value ((JY5).part 2)) (dMul (JY5).value ((JC2).part 2)) from rfl, ev_C2, ev_Y5, p2_C2, p2_Y5]
  rfl

def JNB : DCJet := DCJetKit.mul JC2 JY6
theorem JNB_mem : JetMem JNB fNB D :=
  DCJetKit.mul_mem (JC2_mem D) (JY6_mem)

theorem op_NB : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rfl

theorem ev_NB : (JNB).value = ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JNB).value = dMul (JC2).value (JY6).value from rfl, ev_C2, ev_Y6]
  exact op_NB

theorem p0_NB : (JNB).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNB).part 0 = dAdd (dMul (JC2).value ((JY6).part 0)) (dMul (JY6).value ((JC2).part 0)) from rfl, ev_C2, ev_Y6, p0_C2, p0_Y6]
  rfl

theorem p1_NB : (JNB).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNB).part 1 = dAdd (dMul (JC2).value ((JY6).part 1)) (dMul (JY6).value ((JC2).part 1)) from rfl, ev_C2, ev_Y6, p1_C2, p1_Y6]
  rfl

theorem p2_NB : (JNB).part 2 = ⟨(198 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JNB).part 2 = dAdd (dMul (JC2).value ((JY6).part 2)) (dMul (JY6).value ((JC2).part 2)) from rfl, ev_C2, ev_Y6, p2_C2, p2_Y6]
  rfl

def JNC : DCJet := DCJetKit.mul JC2 JY4
theorem JNC_mem : JetMem JNC fNC D :=
  DCJetKit.mul_mem (JC2_mem D) (JY4_mem)

theorem op_NC : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rfl

theorem ev_NC : (JNC).value = ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JNC).value = dMul (JC2).value (JY4).value from rfl, ev_C2, ev_Y4]
  exact op_NC

theorem p0_NC : (JNC).part 0 = ⟨(198 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JNC).part 0 = dAdd (dMul (JC2).value ((JY4).part 0)) (dMul (JY4).value ((JC2).part 0)) from rfl, ev_C2, ev_Y4, p0_C2, p0_Y4]
  rfl

theorem p1_NC : (JNC).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNC).part 1 = dAdd (dMul (JC2).value ((JY4).part 1)) (dMul (JY4).value ((JC2).part 1)) from rfl, ev_C2, ev_Y4, p1_C2, p1_Y4]
  rfl

theorem p2_NC : (JNC).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JNC).part 2 = dAdd (dMul (JC2).value ((JY4).part 2)) (dMul (JY4).value ((JC2).part 2)) from rfl, ev_C2, ev_Y4, p2_C2, p2_Y4]
  rfl

def JY4CH : DCJet := DCJetKit.mul JY4 JCH
theorem JY4CH_mem : JetMem JY4CH fY4CH D :=
  DCJetKit.mul_mem (JY4_mem) (JCH_mem D)

theorem op_Y4CH : dMul ⟨(200 : ℤ), (4049483871532655494365744472699729758355951544332637944959467 : ℤ), (4049483871533651860230706817030176796531686758792705811703733 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rfl

theorem ev_Y4CH : (JY4CH).value = ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ := by
  rw [show (JY4CH).value = dMul (JY4).value (JCH).value from rfl, ev_Y4, ev_CH]
  exact op_Y4CH

theorem p0_Y4CH : (JY4CH).part 0 = ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JY4CH).part 0 = dAdd (dMul (JY4).value ((JCH).part 0)) (dMul (JCH).value ((JY4).part 0)) from rfl, ev_Y4, ev_CH, p0_Y4, p0_CH]
  rfl

theorem p1_Y4CH : (JY4CH).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4CH).part 1 = dAdd (dMul (JY4).value ((JCH).part 1)) (dMul (JCH).value ((JY4).part 1)) from rfl, ev_Y4, ev_CH, p1_Y4, p1_CH]
  rfl

theorem p2_Y4CH : (JY4CH).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY4CH).part 2 = dAdd (dMul (JY4).value ((JCH).part 2)) (dMul (JCH).value ((JY4).part 2)) from rfl, ev_Y4, ev_CH, p2_Y4, p2_CH]
  rfl

def JY5CH : DCJet := DCJetKit.mul JY5 JCH
theorem JY5CH_mem : JetMem JY5CH fY5CH D :=
  DCJetKit.mul_mem (JY5_mem) (JCH_mem D)

theorem op_Y5CH : dMul ⟨(200 : ℤ), (3657176895331534926107553882173950532625280555789666908403972 : ℤ), (3734842111502011420851541171028160066896758316960222749146863 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rfl

theorem ev_Y5CH : (JY5CH).value = ⟨(199 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ := by
  rw [show (JY5CH).value = dMul (JY5).value (JCH).value from rfl, ev_Y5, ev_CH]
  exact op_Y5CH

theorem p0_Y5CH : (JY5CH).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5CH).part 0 = dAdd (dMul (JY5).value ((JCH).part 0)) (dMul (JCH).value ((JY5).part 0)) from rfl, ev_Y5, ev_CH, p0_Y5, p0_CH]
  rfl

theorem p1_Y5CH : (JY5CH).part 1 = ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JY5CH).part 1 = dAdd (dMul (JY5).value ((JCH).part 1)) (dMul (JCH).value ((JY5).part 1)) from rfl, ev_Y5, ev_CH, p1_Y5, p1_CH]
  rfl

theorem p2_Y5CH : (JY5CH).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY5CH).part 2 = dAdd (dMul (JY5).value ((JCH).part 2)) (dMul (JCH).value ((JY5).part 2)) from rfl, ev_Y5, ev_CH, p2_Y5, p2_CH]
  rfl

def JY6CH : DCJet := DCJetKit.mul JY6 JCH
theorem JY6CH_mem : JetMem JY6CH fY6CH D :=
  DCJetKit.mul_mem (JY6_mem) (JCH_mem D)

theorem op_Y6CH : dMul ⟨(200 : ℤ), (3697021906849702090774160988178878465989773336804422257896241 : ℤ), (3786260064126602103902664808873744373940916659619106874140858 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rfl

theorem ev_Y6CH : (JY6CH).value = ⟨(199 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ := by
  rw [show (JY6CH).value = dMul (JY6).value (JCH).value from rfl, ev_Y6, ev_CH]
  exact op_Y6CH

theorem p0_Y6CH : (JY6CH).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6CH).part 0 = dAdd (dMul (JY6).value ((JCH).part 0)) (dMul (JCH).value ((JY6).part 0)) from rfl, ev_Y6, ev_CH, p0_Y6, p0_CH]
  rfl

theorem p1_Y6CH : (JY6CH).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JY6CH).part 1 = dAdd (dMul (JY6).value ((JCH).part 1)) (dMul (JCH).value ((JY6).part 1)) from rfl, ev_Y6, ev_CH, p1_Y6, p1_CH]
  rfl

theorem p2_Y6CH : (JY6CH).part 2 = ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JY6CH).part 2 = dAdd (dMul (JY6).value ((JCH).part 2)) (dMul (JCH).value ((JY6).part 2)) from rfl, ev_Y6, ev_CH, p2_Y6, p2_CH]
  rfl

def JCH0m4 : DCJet := DCJetKit.sub JCH0 JY4CH
theorem JCH0m4_mem : JetMem JCH0m4 fCH0m4 D :=
  DCJetKit.sub_mem (JCH0_mem D) (JY4CH_mem)

theorem op_CH0m4 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩) = ⟨(199 : ℤ), (-249091466240586082611759543933803615016966686068 : ℤ), (2 : ℤ)⟩ := by
  rfl

theorem ev_CH0m4 : (JCH0m4).value = ⟨(199 : ℤ), (-249091466240586082611759543933803615016966686068 : ℤ), (2 : ℤ)⟩ := by
  rw [show (JCH0m4).value = dAdd (JCH0).value (dNeg (JY4CH).value) from rfl, ev_CH0, ev_Y4CH]
  exact op_CH0m4

theorem p0_CH0m4 : (JCH0m4).part 0 = ⟨(200 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JCH0m4).part 0 = dAdd ((JCH0).part 0) (dNeg ((JY4CH).part 0)) from rfl, p0_CH0, p0_Y4CH]
  rfl

theorem p1_CH0m4 : (JCH0m4).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m4).part 1 = dAdd ((JCH0).part 1) (dNeg ((JY4CH).part 1)) from rfl, p1_CH0, p1_Y4CH]
  rfl

theorem p2_CH0m4 : (JCH0m4).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m4).part 2 = dAdd ((JCH0).part 2) (dNeg ((JY4CH).part 2)) from rfl, p2_CH0, p2_Y4CH]
  rfl

def JCH0m5 : DCJet := DCJetKit.sub JCH0 JY5CH
theorem JCH0m5_mem : JetMem JCH0m5 fCH0m5 D :=
  DCJetKit.sub_mem (JCH0_mem D) (JY5CH_mem)

theorem op_CH0m5 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩) = ⟨(199 : ℤ), (78660440007661018378550825417892422864798306843103798953150 : ℤ), (98076744050280142064547647631444806432667747135742759138875 : ℤ)⟩ := by
  rfl

theorem ev_CH0m5 : (JCH0m5).value = ⟨(199 : ℤ), (78660440007661018378550825417892422864798306843103798953150 : ℤ), (98076744050280142064547647631444806432667747135742759138875 : ℤ)⟩ := by
  rw [show (JCH0m5).value = dAdd (JCH0).value (dNeg (JY5CH).value) from rfl, ev_CH0, ev_Y5CH]
  exact op_CH0m5

theorem p0_CH0m5 : (JCH0m5).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m5).part 0 = dAdd ((JCH0).part 0) (dNeg ((JY5CH).part 0)) from rfl, p0_CH0, p0_Y5CH]
  rfl

theorem p1_CH0m5 : (JCH0m5).part 1 = ⟨(200 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JCH0m5).part 1 = dAdd ((JCH0).part 1) (dNeg ((JY5CH).part 1)) from rfl, p1_CH0, p1_Y5CH]
  rfl

theorem p2_CH0m5 : (JCH0m5).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m5).part 2 = dAdd ((JCH0).part 2) (dNeg ((JY5CH).part 2)) from rfl, p2_CH0, p2_Y5CH]
  rfl

def JCH0m6 : DCJet := DCJetKit.sub JCH0 JY6CH
theorem JCH0m6_mem : JetMem JCH0m6 fCH0m6 D :=
  DCJetKit.sub_mem (JCH0_mem D) (JY6CH_mem)

theorem op_CH0m6 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩) = ⟨(199 : ℤ), (65805951851513347615769915956496346103758721178382767704651 : ℤ), (88115491170738350897895871130212823091544551882053921765808 : ℤ)⟩ := by
  rfl

theorem ev_CH0m6 : (JCH0m6).value = ⟨(199 : ℤ), (65805951851513347615769915956496346103758721178382767704651 : ℤ), (88115491170738350897895871130212823091544551882053921765808 : ℤ)⟩ := by
  rw [show (JCH0m6).value = dAdd (JCH0).value (dNeg (JY6CH).value) from rfl, ev_CH0, ev_Y6CH]
  exact op_CH0m6

theorem p0_CH0m6 : (JCH0m6).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m6).part 0 = dAdd ((JCH0).part 0) (dNeg ((JY6CH).part 0)) from rfl, p0_CH0, p0_Y6CH]
  rfl

theorem p1_CH0m6 : (JCH0m6).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JCH0m6).part 1 = dAdd ((JCH0).part 1) (dNeg ((JY6CH).part 1)) from rfl, p1_CH0, p1_Y6CH]
  rfl

theorem p2_CH0m6 : (JCH0m6).part 2 = ⟨(200 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ), (-803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ := by
  rw [show (JCH0m6).part 2 = dAdd ((JCH0).part 2) (dNeg ((JY6CH).part 2)) from rfl, p2_CH0, p2_Y6CH]
  rfl

def JLf4 : DCJet := DCJetKit.mul JCH0m4 JCH0i
theorem JLf4_mem : JetMem JLf4 fLf4 D :=
  DCJetKit.mul_mem (JCH0m4_mem) (JCH0i_mem D)

theorem op_Lf4 : dMul ⟨(199 : ℤ), (-249091466240586082611759543933803615016966686068 : ℤ), (2 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(239 : ℤ), (-1053380628889605211264257483039076150532377995602273311633724 : ℤ), (8457781752124 : ℤ)⟩ := by
  rfl

theorem ev_Lf4 : (JLf4).value = ⟨(239 : ℤ), (-1053380628889605211264257483039076150532377995602273311633724 : ℤ), (8457781752124 : ℤ)⟩ := by
  rw [show (JLf4).value = dMul (JCH0m4).value (JCH0i).value from rfl, ev_CH0m4, ev_CH0i]
  exact op_Lf4

theorem p0_Lf4 : (JLf4).part 0 = ⟨(199 : ℤ), (-1545132734864413726482655858020348656271349032483454649328247 : ℤ), (-1545132734864413726482655858020348656271349032483454649328245 : ℤ)⟩ := by
  rw [show (JLf4).part 0 = dAdd (dMul (JCH0m4).value ((JCH0i).part 0)) (dMul (JCH0i).value ((JCH0m4).part 0)) from rfl, ev_CH0m4, ev_CH0i, p0_CH0m4, p0_CH0i]
  rfl

theorem p1_Lf4 : (JLf4).part 1 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf4).part 1 = dAdd (dMul (JCH0m4).value ((JCH0i).part 1)) (dMul (JCH0i).value ((JCH0m4).part 1)) from rfl, ev_CH0m4, ev_CH0i, p1_CH0m4, p1_CH0i]
  rfl

theorem p2_Lf4 : (JLf4).part 2 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf4).part 2 = dAdd (dMul (JCH0m4).value ((JCH0i).part 2)) (dMul (JCH0i).value ((JCH0m4).part 2)) from rfl, ev_CH0m4, ev_CH0i, p2_CH0m4, p2_CH0i]
  rfl

def JLf5 : DCJet := DCJetKit.mul JCH0m5 JCH0i
theorem JLf5_mem : JetMem JLf5 fLf5 D :=
  DCJetKit.mul_mem (JCH0m5_mem) (JCH0i_mem D)

theorem op_Lf5 : dMul ⟨(199 : ℤ), (78660440007661018378550825417892422864798306843103798953150 : ℤ), (98076744050280142064547647631444806432667747135742759138875 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(201 : ℤ), (1210160615502477205823858852582960351766127797586212291586922 : ℤ), (1508872985388925262531502271252997022041042263626811679059617 : ℤ)⟩ := by
  rfl

theorem ev_Lf5 : (JLf5).value = ⟨(201 : ℤ), (1210160615502477205823858852582960351766127797586212291586922 : ℤ), (1508872985388925262531502271252997022041042263626811679059617 : ℤ)⟩ := by
  rw [show (JLf5).value = dMul (JCH0m5).value (JCH0i).value from rfl, ev_CH0m5, ev_CH0i]
  exact op_Lf5

theorem p0_Lf5 : (JLf5).part 0 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf5).part 0 = dAdd (dMul (JCH0m5).value ((JCH0i).part 0)) (dMul (JCH0i).value ((JCH0m5).part 0)) from rfl, ev_CH0m5, ev_CH0i, p0_CH0m5, p0_CH0i]
  rfl

theorem p1_Lf5 : (JLf5).part 1 = ⟨(199 : ℤ), (-1545132734864413726482655858020348656271349032483454649328247 : ℤ), (-1545132734864413726482655858020348656271349032483454649328245 : ℤ)⟩ := by
  rw [show (JLf5).part 1 = dAdd (dMul (JCH0m5).value ((JCH0i).part 1)) (dMul (JCH0i).value ((JCH0m5).part 1)) from rfl, ev_CH0m5, ev_CH0i, p1_CH0m5, p1_CH0i]
  rfl

theorem p2_Lf5 : (JLf5).part 2 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf5).part 2 = dAdd (dMul (JCH0m5).value ((JCH0i).part 2)) (dMul (JCH0i).value ((JCH0m5).part 2)) from rfl, ev_CH0m5, ev_CH0i, p2_CH0m5, p2_CH0i]
  rfl

def JLf6 : DCJet := DCJetKit.mul JCH0m6 JCH0i
theorem JLf6_mem : JetMem JLf6 fLf6 D :=
  DCJetKit.mul_mem (JCH0m6_mem) (JCH0i_mem D)

theorem op_Lf6 : dMul ⟨(199 : ℤ), (65805951851513347615769915956496346103758721178382767704651 : ℤ), (88115491170738350897895871130212823091544551882053921765808 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(201 : ℤ), (1012399259254051501781075630099943786211672633513581041610014 : ℤ), (1355622941088282321506090325080197278331454644339291104089355 : ℤ)⟩ := by
  rfl

theorem ev_Lf6 : (JLf6).value = ⟨(201 : ℤ), (1012399259254051501781075630099943786211672633513581041610014 : ℤ), (1355622941088282321506090325080197278331454644339291104089355 : ℤ)⟩ := by
  rw [show (JLf6).value = dMul (JCH0m6).value (JCH0i).value from rfl, ev_CH0m6, ev_CH0i]
  exact op_Lf6

theorem p0_Lf6 : (JLf6).part 0 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf6).part 0 = dAdd (dMul (JCH0m6).value ((JCH0i).part 0)) (dMul (JCH0i).value ((JCH0m6).part 0)) from rfl, ev_CH0m6, ev_CH0i, p0_CH0m6, p0_CH0i]
  rfl

theorem p1_Lf6 : (JLf6).part 1 = ⟨(398 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JLf6).part 1 = dAdd (dMul (JCH0m6).value ((JCH0i).part 1)) (dMul (JCH0i).value ((JCH0m6).part 1)) from rfl, ev_CH0m6, ev_CH0i, p1_CH0m6, p1_CH0i]
  rfl

theorem p2_Lf6 : (JLf6).part 2 = ⟨(199 : ℤ), (-1545132734864413726482655858020348656271349032483454649328247 : ℤ), (-1545132734864413726482655858020348656271349032483454649328245 : ℤ)⟩ := by
  rw [show (JLf6).part 2 = dAdd (dMul (JCH0m6).value ((JCH0i).part 2)) (dMul (JCH0i).value ((JCH0m6).part 2)) from rfl, ev_CH0m6, ev_CH0i, p2_CH0m6, p2_CH0i]
  rfl

def JINVPI : DCJet := DCJetKit.inv JPI
theorem JINVPI_mem : JetMem JINVPI fINVPI D :=
  DCJetKit.inv_mem (JPI_mem D) (by rw [ev_PI]; decide)

theorem op_INVPI : dInv ⟨(40 : ℤ), (3454217652357 : ℤ), (3454217652358 : ℤ)⟩ = ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ := by
  rfl

theorem ev_INVPI : (JINVPI).value = ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ := by
  rw [show (JINVPI).value = dInv (JPI).value from rfl, ev_PI]
  exact op_INVPI

theorem p0_INVPI : (JINVPI).part 0 = ⟨(203 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JINVPI).part 0 = dNeg (dMul (dMul (dInv (JPI).value) (dInv (JPI).value)) ((JPI).part 0)) from rfl, ev_PI, op_INVPI, p0_PI]
  rfl

theorem p1_INVPI : (JINVPI).part 1 = ⟨(203 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JINVPI).part 1 = dNeg (dMul (dMul (dInv (JPI).value) (dInv (JPI).value)) ((JPI).part 1)) from rfl, ev_PI, op_INVPI, p1_PI]
  rfl

theorem p2_INVPI : (JINVPI).part 2 = ⟨(203 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JINVPI).part 2 = dNeg (dMul (dMul (dInv (JPI).value) (dInv (JPI).value)) ((JPI).part 2)) from rfl, ev_PI, op_INVPI, p2_PI]
  rfl

def JC2MM1 : DCJet := DCJetKit.mul JC2 JMM1
theorem JC2MM1_mem : JetMem JC2MM1 fC2MM1 D :=
  DCJetKit.mul_mem (JC2_mem D) (JMM1_mem D)

theorem op_C2MM1 : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(200 : ℤ), (1626351141384074285262729427986317719690753223710083998986084 : ℤ), (1626351302077878711161756982182526953807013475930383377265369 : ℤ)⟩ = ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ := by
  rfl

theorem ev_C2MM1 : (JC2MM1).value = ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ := by
  rw [show (JC2MM1).value = dMul (JC2).value (JMM1).value from rfl, ev_C2, ev_MM1]
  exact op_C2MM1

theorem p0_C2MM1 : (JC2MM1).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC2MM1).part 0 = dAdd (dMul (JC2).value ((JMM1).part 0)) (dMul (JMM1).value ((JC2).part 0)) from rfl, ev_C2, ev_MM1, p0_C2, p0_MM1]
  rfl

theorem p1_C2MM1 : (JC2MM1).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC2MM1).part 1 = dAdd (dMul (JC2).value ((JMM1).part 1)) (dMul (JMM1).value ((JC2).part 1)) from rfl, ev_C2, ev_MM1, p1_C2, p1_MM1]
  rfl

theorem p2_C2MM1 : (JC2MM1).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC2MM1).part 2 = dAdd (dMul (JC2).value ((JMM1).part 2)) (dMul (JMM1).value ((JC2).part 2)) from rfl, ev_C2, ev_MM1, p2_C2, p2_MM1]
  rfl

def JK1 : DCJet := DCJetKit.mul JC2MM1 JINVPI
theorem JK1_mem : JetMem JK1 fK1 D :=
  DCJetKit.mul_mem (JC2MM1_mem) (JINVPI_mem)

theorem op_K1 : dMul ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ = ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ := by
  rfl

theorem ev_K1 : (JK1).value = ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ := by
  rw [show (JK1).value = dMul (JC2MM1).value (JINVPI).value from rfl, ev_C2MM1, ev_INVPI]
  exact op_K1

theorem p0_K1 : (JK1).part 0 = ⟨(401 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK1).part 0 = dAdd (dMul (JC2MM1).value ((JINVPI).part 0)) (dMul (JINVPI).value ((JC2MM1).part 0)) from rfl, ev_C2MM1, ev_INVPI, p0_C2MM1, p0_INVPI]
  rfl

theorem p1_K1 : (JK1).part 1 = ⟨(401 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK1).part 1 = dAdd (dMul (JC2MM1).value ((JINVPI).part 1)) (dMul (JINVPI).value ((JC2MM1).part 1)) from rfl, ev_C2MM1, ev_INVPI, p1_C2MM1, p1_INVPI]
  rfl

theorem p2_K1 : (JK1).part 2 = ⟨(401 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK1).part 2 = dAdd (dMul (JC2MM1).value ((JINVPI).part 2)) (dMul (JINVPI).value ((JC2MM1).part 2)) from rfl, ev_C2MM1, ev_INVPI, p2_C2MM1, p2_INVPI]
  rfl

def JC8MM2 : DCJet := DCJetKit.mul JC8 JMM2
theorem JC8MM2_mem : JetMem JC8MM2 fC8MM2 D :=
  DCJetKit.mul_mem (JC8_mem D) (JMM2_mem D)

theorem op_C8MM2 : dMul ⟨(0 : ℤ), (8 : ℤ), (8 : ℤ)⟩ ⟨(200 : ℤ), (40839526925820108357761195595804476961800527985492788512766 : ℤ), (40839542995200550947663951015425400373426553207522726340696 : ℤ)⟩ = ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ := by
  rfl

theorem ev_C8MM2 : (JC8MM2).value = ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ := by
  rw [show (JC8MM2).value = dMul (JC8).value (JMM2).value from rfl, ev_C8, ev_MM2]
  exact op_C8MM2

theorem p0_C8MM2 : (JC8MM2).part 0 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC8MM2).part 0 = dAdd (dMul (JC8).value ((JMM2).part 0)) (dMul (JMM2).value ((JC8).part 0)) from rfl, ev_C8, ev_MM2, p0_C8, p0_MM2]
  rfl

theorem p1_C8MM2 : (JC8MM2).part 1 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC8MM2).part 1 = dAdd (dMul (JC8).value ((JMM2).part 1)) (dMul (JMM2).value ((JC8).part 1)) from rfl, ev_C8, ev_MM2, p1_C8, p1_MM2]
  rfl

theorem p2_C8MM2 : (JC8MM2).part 2 = ⟨(200 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JC8MM2).part 2 = dAdd (dMul (JC8).value ((JMM2).part 2)) (dMul (JMM2).value ((JC8).part 2)) from rfl, ev_C8, ev_MM2, p2_C8, p2_MM2]
  rfl

def JK2 : DCJet := DCJetKit.mul JC8MM2 JINVPI
theorem JK2_mem : JetMem JK2 fK2 D :=
  DCJetKit.mul_mem (JC8MM2_mem) (JINVPI_mem)

theorem op_K2 : dMul ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ = ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ := by
  rfl

theorem ev_K2 : (JK2).value = ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ := by
  rw [show (JK2).value = dMul (JC8MM2).value (JINVPI).value from rfl, ev_C8MM2, ev_INVPI]
  exact op_K2

theorem p0_K2 : (JK2).part 0 = ⟨(403 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK2).part 0 = dAdd (dMul (JC8MM2).value ((JINVPI).part 0)) (dMul (JINVPI).value ((JC8MM2).part 0)) from rfl, ev_C8MM2, ev_INVPI, p0_C8MM2, p0_INVPI]
  rfl

theorem p1_K2 : (JK2).part 1 = ⟨(403 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK2).part 1 = dAdd (dMul (JC8MM2).value ((JINVPI).part 1)) (dMul (JINVPI).value ((JC8MM2).part 1)) from rfl, ev_C8MM2, ev_INVPI, p1_C8MM2, p1_INVPI]
  rfl

theorem p2_K2 : (JK2).part 2 = ⟨(403 : ℤ), (0 : ℤ), (0 : ℤ)⟩ := by
  rw [show (JK2).part 2 = dAdd (dMul (JC8MM2).value ((JINVPI).part 2)) (dMul (JINVPI).value ((JC8MM2).part 2)) from rfl, ev_C8MM2, ev_INVPI, p2_C8MM2, p2_INVPI]
  rfl

def JAsq : DCJet := DCJetKit.mul JA JA
theorem JAsq_mem : JetMem JAsq fAsq D :=
  DCJetKit.mul_mem (JA_mem) (JA_mem)

theorem op_Asq : dMul ⟨(195 : ℤ), (1310190349648086688609276427437736092310671362412139342631099 : ℤ), (1357690902654081626216419595205048512860410608729347869873497 : ℤ)⟩ ⟨(195 : ℤ), (1310190349648086688609276427437736092310671362412139342631099 : ℤ), (1357690902654081626216419595205048512860410608729347869873497 : ℤ)⟩ = ⟨(190 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ := by
  rfl

theorem ev_Asq : (JAsq).value = ⟨(190 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ := by
  rw [show (JAsq).value = dMul (JA).value (JA).value from rfl, ev_A]
  exact op_Asq

theorem p0_Asq : (JAsq).part 0 = ⟨(190 : ℤ), (1237093918084875603799365448574294300501396853013816578935904 : ℤ), (1307512118441736411287527388577434055827990183470316430269881 : ℤ)⟩ := by
  rw [show (JAsq).part 0 = dAdd (dMul (JA).value ((JA).part 0)) (dMul (JA).value ((JA).part 0)) from rfl, ev_A, p0_A]
  rfl

theorem p1_Asq : (JAsq).part 1 = ⟨(190 : ℤ), (1285031754155843795154992769984344178938487568392282591522579 : ℤ), (1347755089964488754064927134731438485849399274693048889586207 : ℤ)⟩ := by
  rw [show (JAsq).part 1 = dAdd (dMul (JA).value ((JA).part 1)) (dMul (JA).value ((JA).part 1)) from rfl, ev_A, p1_A]
  rfl

theorem p2_Asq : (JAsq).part 2 = ⟨(192 : ℤ), (-1131012025028782197763735924851349778395101233262734944219944 : ℤ), (-1065717982574030515584911254706688434488772397519818884424692 : ℤ)⟩ := by
  rw [show (JAsq).part 2 = dAdd (dMul (JA).value ((JA).part 2)) (dMul (JA).value ((JA).part 2)) from rfl, ev_A, p2_A]
  rfl

def JF4A : DCJet := DCJetKit.mul JC4 JAsq
theorem JF4A_mem : JetMem JF4A fF4A D :=
  DCJetKit.mul_mem (JC4_mem D) (JAsq_mem)

theorem op_F4A : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ = ⟨(188 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ := by
  rfl

theorem ev_F4A : (JF4A).value = ⟨(188 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ := by
  rw [show (JF4A).value = dMul (JC4).value (JAsq).value from rfl, ev_C4, ev_Asq]
  exact op_F4A

theorem p0_F4A : (JF4A).part 0 = ⟨(188 : ℤ), (1237093918084875603799365448574294300501396853013816578935904 : ℤ), (1307512118441736411287527388577434055827990183470316430269881 : ℤ)⟩ := by
  rw [show (JF4A).part 0 = dAdd (dMul (JC4).value ((JAsq).part 0)) (dMul (JAsq).value ((JC4).part 0)) from rfl, ev_C4, ev_Asq, p0_C4, p0_Asq]
  rfl

theorem p1_F4A : (JF4A).part 1 = ⟨(188 : ℤ), (1285031754155843795154992769984344178938487568392282591522579 : ℤ), (1347755089964488754064927134731438485849399274693048889586207 : ℤ)⟩ := by
  rw [show (JF4A).part 1 = dAdd (dMul (JC4).value ((JAsq).part 1)) (dMul (JAsq).value ((JC4).part 1)) from rfl, ev_C4, ev_Asq, p1_C4, p1_Asq]
  rfl

theorem p2_F4A : (JF4A).part 2 = ⟨(190 : ℤ), (-1131012025028782197763735924851349778395101233262734944219944 : ℤ), (-1065717982574030515584911254706688434488772397519818884424692 : ℤ)⟩ := by
  rw [show (JF4A).part 2 = dAdd (dMul (JC4).value ((JAsq).part 2)) (dMul (JAsq).value ((JC4).part 2)) from rfl, ev_C4, ev_Asq, p2_C4, p2_Asq]
  rfl

def JBsq : DCJet := DCJetKit.mul JB JB
theorem JBsq_mem : JetMem JBsq fBsq D :=
  DCJetKit.mul_mem (JB_mem) (JB_mem)

theorem op_Bsq : dMul ⟨(195 : ℤ), (1119886522603568120731881860118615247481823501238675430013657 : ℤ), (1195916663905892051976153956058604262341990085187101712960850 : ℤ)⟩ ⟨(195 : ℤ), (1119886522603568120731881860118615247481823501238675430013657 : ℤ), (1195916663905892051976153956058604262341990085187101712960850 : ℤ)⟩ = ⟨(190 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ := by
  rfl

theorem ev_Bsq : (JBsq).value = ⟨(190 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ := by
  rw [show (JBsq).value = dMul (JB).value (JB).value from rfl, ev_B]
  exact op_Bsq

theorem p0_Bsq : (JBsq).part 0 = ⟨(192 : ℤ), (-1065507386305392547001776385580305109338739201524340521230057 : ℤ), (-997767986408430112389083619516612500143137547694504484407495 : ℤ)⟩ := by
  rw [show (JBsq).part 0 = dAdd (dMul (JB).value ((JB).part 0)) (dMul (JB).value ((JB).part 0)) from rfl, ev_B, p0_B]
  rfl

theorem p1_Bsq : (JBsq).part 1 = ⟨(190 : ℤ), (1004728195915919478200708894504932767991120985940025505592051 : ℤ), (1111542411047744692579531673478643490038913739258046449022797 : ℤ)⟩ := by
  rw [show (JBsq).part 1 = dAdd (dMul (JB).value ((JB).part 1)) (dMul (JB).value ((JB).part 1)) from rfl, ev_B, p1_B]
  rfl

theorem p2_Bsq : (JBsq).part 2 = ⟨(190 : ℤ), (1000756873961707756929410223094178004341446791560049994114354 : ℤ), (1105945493075923210591936606336903521890994065894359253354473 : ℤ)⟩ := by
  rw [show (JBsq).part 2 = dAdd (dMul (JB).value ((JB).part 2)) (dMul (JB).value ((JB).part 2)) from rfl, ev_B, p2_B]
  rfl

def JF4B : DCJet := DCJetKit.mul JC4 JBsq
theorem JF4B_mem : JetMem JF4B fF4B D :=
  DCJetKit.mul_mem (JC4_mem D) (JBsq_mem)

theorem op_F4B : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ = ⟨(188 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ := by
  rfl

theorem ev_F4B : (JF4B).value = ⟨(188 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ := by
  rw [show (JF4B).value = dMul (JC4).value (JBsq).value from rfl, ev_C4, ev_Bsq]
  exact op_F4B

theorem p0_F4B : (JF4B).part 0 = ⟨(190 : ℤ), (-1065507386305392547001776385580305109338739201524340521230057 : ℤ), (-997767986408430112389083619516612500143137547694504484407495 : ℤ)⟩ := by
  rw [show (JF4B).part 0 = dAdd (dMul (JC4).value ((JBsq).part 0)) (dMul (JBsq).value ((JC4).part 0)) from rfl, ev_C4, ev_Bsq, p0_C4, p0_Bsq]
  rfl

theorem p1_F4B : (JF4B).part 1 = ⟨(188 : ℤ), (1004728195915919478200708894504932767991120985940025505592051 : ℤ), (1111542411047744692579531673478643490038913739258046449022797 : ℤ)⟩ := by
  rw [show (JF4B).part 1 = dAdd (dMul (JC4).value ((JBsq).part 1)) (dMul (JBsq).value ((JC4).part 1)) from rfl, ev_C4, ev_Bsq, p1_C4, p1_Bsq]
  rfl

theorem p2_F4B : (JF4B).part 2 = ⟨(188 : ℤ), (1000756873961707756929410223094178004341446791560049994114354 : ℤ), (1105945493075923210591936606336903521890994065894359253354473 : ℤ)⟩ := by
  rw [show (JF4B).part 2 = dAdd (dMul (JC4).value ((JBsq).part 2)) (dMul (JBsq).value ((JC4).part 2)) from rfl, ev_C4, ev_Bsq, p2_C4, p2_Bsq]
  rfl

def JCsq : DCJet := DCJetKit.mul JC JC
theorem JCsq_mem : JetMem JCsq fCsq D :=
  DCJetKit.mul_mem (JC_mem) (JC_mem)

theorem op_Csq : dMul ⟨(195 : ℤ), (1335108833817039519080090543859417568596208511869928248159277 : ℤ), (1387342317744129399973935671924094705106485942740566760057855 : ℤ)⟩ ⟨(195 : ℤ), (1335108833817039519080090543859417568596208511869928248159277 : ℤ), (1387342317744129399973935671924094705106485942740566760057855 : ℤ)⟩ = ⟨(190 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ := by
  rfl

theorem ev_Csq : (JCsq).value = ⟨(190 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ := by
  rw [show (JCsq).value = dMul (JC).value (JC).value from rfl, ev_C]
  exact op_Csq

theorem p0_Csq : (JCsq).part 0 = ⟨(190 : ℤ), (1273496816628093150893220028133162113586508855781268243038017 : ℤ), (1353475782902994422527235750036002177044999757570175660752292 : ℤ)⟩ := by
  rw [show (JCsq).part 0 = dAdd (dMul (JC).value ((JC).part 0)) (dMul (JC).value ((JC).part 0)) from rfl, ev_C, p0_C]
  rfl

theorem p1_Csq : (JCsq).part 1 = ⟨(192 : ℤ), (-1140018120124449983391839197457051277096462430491124722165835 : ℤ), (-1074282523231358105880133362947643126469323046899878504111413 : ℤ)⟩ := by
  rw [show (JCsq).part 1 = dAdd (dMul (JC).value ((JC).part 1)) (dMul (JC).value ((JC).part 1)) from rfl, ev_C, p1_C]
  rfl

theorem p2_Csq : (JCsq).part 2 = ⟨(190 : ℤ), (1317611841907397732228947962521086784159527946710266184183547 : ℤ), (1388104849985001712267861563608152997444326503789109148244782 : ℤ)⟩ := by
  rw [show (JCsq).part 2 = dAdd (dMul (JC).value ((JC).part 2)) (dMul (JC).value ((JC).part 2)) from rfl, ev_C, p2_C]
  rfl

def JF4C : DCJet := DCJetKit.mul JC4 JCsq
theorem JF4C_mem : JetMem JF4C fF4C D :=
  DCJetKit.mul_mem (JC4_mem D) (JCsq_mem)

theorem op_F4C : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ = ⟨(188 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ := by
  rfl

theorem ev_F4C : (JF4C).value = ⟨(188 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ := by
  rw [show (JF4C).value = dMul (JC4).value (JCsq).value from rfl, ev_C4, ev_Csq]
  exact op_F4C

theorem p0_F4C : (JF4C).part 0 = ⟨(188 : ℤ), (1273496816628093150893220028133162113586508855781268243038017 : ℤ), (1353475782902994422527235750036002177044999757570175660752292 : ℤ)⟩ := by
  rw [show (JF4C).part 0 = dAdd (dMul (JC4).value ((JCsq).part 0)) (dMul (JCsq).value ((JC4).part 0)) from rfl, ev_C4, ev_Csq, p0_C4, p0_Csq]
  rfl

theorem p1_F4C : (JF4C).part 1 = ⟨(190 : ℤ), (-1140018120124449983391839197457051277096462430491124722165835 : ℤ), (-1074282523231358105880133362947643126469323046899878504111413 : ℤ)⟩ := by
  rw [show (JF4C).part 1 = dAdd (dMul (JC4).value ((JCsq).part 1)) (dMul (JCsq).value ((JC4).part 1)) from rfl, ev_C4, ev_Csq, p1_C4, p1_Csq]
  rfl

theorem p2_F4C : (JF4C).part 2 = ⟨(188 : ℤ), (1317611841907397732228947962521086784159527946710266184183547 : ℤ), (1388104849985001712267861563608152997444326503789109148244782 : ℤ)⟩ := by
  rw [show (JF4C).part 2 = dAdd (dMul (JC4).value ((JCsq).part 2)) (dMul (JCsq).value ((JC4).part 2)) from rfl, ev_C4, ev_Csq, p2_C4, p2_Csq]
  rfl

def JD4Asq : DCJet := DCJetKit.mul JD4A JD4A
theorem JD4Asq_mem : JetMem JD4Asq fD4Asq D :=
  DCJetKit.mul_mem (JD4A_mem) (JD4A_mem)

theorem op_D4Asq : dMul ⟨(194 : ℤ), (811718362051959021221070227209858817434547300696546197227828 : ℤ), (911791162911414164264663553772158721208345175519987873310647 : ℤ)⟩ ⟨(194 : ℤ), (811718362051959021221070227209858817434547300696546197227828 : ℤ), (911791162911414164264663553772158721208345175519987873310647 : ℤ)⟩ = ⟨(189 : ℤ), (820052399215115512916807310144445507363799132612851946717071 : ℤ), (1034717085370539865198315855805099518773257762560806878561085 : ℤ)⟩ := by
  rfl

theorem ev_D4Asq : (JD4Asq).value = ⟨(189 : ℤ), (820052399215115512916807310144445507363799132612851946717071 : ℤ), (1034717085370539865198315855805099518773257762560806878561085 : ℤ)⟩ := by
  rw [show (JD4Asq).value = dMul (JD4A).value (JD4A).value from rfl, ev_D4A]
  exact op_D4Asq

theorem p0_D4Asq : (JD4Asq).part 0 = ⟨(189 : ℤ), (1324370789513999886321102101928729400751592533204953568793808 : ℤ), (1551501360792675885260373351802478083847239456517908913618929 : ℤ)⟩ := by
  rw [show (JD4Asq).part 0 = dAdd (dMul (JD4A).value ((JD4A).part 0)) (dMul (JD4A).value ((JD4A).part 0)) from rfl, ev_D4A, p0_D4A]
  rfl

theorem p1_D4Asq : (JD4Asq).part 1 = ⟨(190 : ℤ), (334806068931373999492110428231705329094844440691353571572102 : ℤ), (874494580775957845425638476764758095771650147558451461673592 : ℤ)⟩ := by
  rw [show (JD4Asq).part 1 = dAdd (dMul (JD4A).value ((JD4A).part 1)) (dMul (JD4A).value ((JD4A).part 1)) from rfl, ev_D4A, p1_D4A]
  rfl

theorem p2_D4Asq : (JD4Asq).part 2 = ⟨(189 : ℤ), (1209099227692925895680615472919859803108311290494823549696751 : ℤ), (1450650954088772278591074566404167642792067020838349190254843 : ℤ)⟩ := by
  rw [show (JD4Asq).part 2 = dAdd (dMul (JD4A).value ((JD4A).part 2)) (dMul (JD4A).value ((JD4A).part 2)) from rfl, ev_D4A, p2_D4A]
  rfl

def JD4Bsq : DCJet := DCJetKit.mul JD4B JD4B
theorem JD4Bsq_mem : JetMem JD4Bsq fD4Bsq D :=
  DCJetKit.mul_mem (JD4B_mem) (JD4B_mem)

theorem op_D4Bsq : dMul ⟨(194 : ℤ), (794517682910748089668306555125200761408368760420833179199617 : ℤ), (900375736678588096163830783243737965166197690220787624436542 : ℤ)⟩ ⟨(194 : ℤ), (794517682910748089668306555125200761408368760420833179199617 : ℤ), (900375736678588096163830783243737965166197690220787624436542 : ℤ)⟩ = ⟨(189 : ℤ), (785666069346136049431761655017997718441333017629462719091635 : ℤ), (1008970408157009751519757639418847141038449364469856854210572 : ℤ)⟩ := by
  rfl

theorem ev_D4Bsq : (JD4Bsq).value = ⟨(189 : ℤ), (785666069346136049431761655017997718441333017629462719091635 : ℤ), (1008970408157009751519757639418847141038449364469856854210572 : ℤ)⟩ := by
  rw [show (JD4Bsq).value = dMul (JD4B).value (JD4B).value from rfl, ev_D4B]
  exact op_D4Bsq

theorem p0_D4Bsq : (JD4Bsq).part 0 = ⟨(189 : ℤ), (1324707220781809632183990704049335667756391459295497369437470 : ℤ), (1574551800117237043368928869949087574050746338710727005183338 : ℤ)⟩ := by
  rw [show (JD4Bsq).part 0 = dAdd (dMul (JD4B).value ((JD4B).part 0)) (dMul (JD4B).value ((JD4B).part 0)) from rfl, ev_D4B, p0_D4B]
  rfl

theorem p1_D4Bsq : (JD4Bsq).part 1 = ⟨(189 : ℤ), (1196371882100732702822546339234339869874187808850035770853139 : ℤ), (1452210344917849873049396302311187840089065651571133114366307 : ℤ)⟩ := by
  rw [show (JD4Bsq).part 1 = dAdd (dMul (JD4B).value ((JD4B).part 1)) (dMul (JD4B).value ((JD4B).part 1)) from rfl, ev_D4B, p1_D4B]
  rfl

theorem p2_D4Bsq : (JD4Bsq).part 2 = ⟨(191 : ℤ), (267470639137360891502809547992620801982203153431260909633139 : ℤ), (1369353220567678620720961373786120609347216558045284990810956 : ℤ)⟩ := by
  rw [show (JD4Bsq).part 2 = dAdd (dMul (JD4B).value ((JD4B).part 2)) (dMul (JD4B).value ((JD4B).part 2)) from rfl, ev_D4B, p2_D4B]
  rfl

def JD4Csq : DCJet := DCJetKit.mul JD4C JD4C
theorem JD4Csq_mem : JetMem JD4Csq fD4Csq D :=
  DCJetKit.mul_mem (JD4C_mem) (JD4C_mem)

theorem op_D4Csq : dMul ⟨(195 : ℤ), (1314562018164287360137992701436860404057508287066124100461832 : ℤ), (1467931010811258200449222572531530043333023059084882674361223 : ℤ)⟩ ⟨(195 : ℤ), (1314562018164287360137992701436860404057508287066124100461832 : ℤ), (1467931010811258200449222572531530043333023059084882674361223 : ℤ)⟩ = ⟨(190 : ℤ), (1075382654467573562147347938397195010863241032107569368443737 : ℤ), (1340948681997891370560080266616017535051408574711033464210594 : ℤ)⟩ := by
  rfl

theorem ev_D4Csq : (JD4Csq).value = ⟨(190 : ℤ), (1075382654467573562147347938397195010863241032107569368443737 : ℤ), (1340948681997891370560080266616017535051408574711033464210594 : ℤ)⟩ := by
  rw [show (JD4Csq).value = dMul (JD4C).value (JD4C).value from rfl, ev_D4C]
  exact op_D4Csq

theorem p0_D4Csq : (JD4Csq).part 0 = ⟨(190 : ℤ), (-1030307987401268673592315926244051820107110667956305241474073 : ℤ), (-723512335364393231778108658048837662731030041098103516775500 : ℤ)⟩ := by
  rw [show (JD4Csq).part 0 = dAdd (dMul (JD4C).value ((JD4C).part 0)) (dMul (JD4C).value ((JD4C).part 0)) from rfl, ev_D4C, p0_D4C]
  rfl

theorem p1_D4Csq : (JD4Csq).part 1 = ⟨(189 : ℤ), (1187432724513822650422834606197455320692629266385099316664313 : ℤ), (1354128436646768909754381627516471588638776565749581059230276 : ℤ)⟩ := by
  rw [show (JD4Csq).part 1 = dAdd (dMul (JD4C).value ((JD4C).part 1)) (dMul (JD4C).value ((JD4C).part 1)) from rfl, ev_D4C, p1_D4C]
  rfl

theorem p2_D4Csq : (JD4Csq).part 2 = ⟨(189 : ℤ), (1200369826529778807799496842319991978155130934981042616529415 : ℤ), (1372770861071803968476645615582249721137714683539709454535234 : ℤ)⟩ := by
  rw [show (JD4Csq).part 2 = dAdd (dMul (JD4C).value ((JD4C).part 2)) (dMul (JD4C).value ((JD4C).part 2)) from rfl, ev_D4C, p2_D4C]
  rfl

def JT4A : DCJet := DCJetKit.inv JF4A
theorem JT4A_mem : JetMem JT4A fT4A D :=
  DCJetKit.inv_mem (JF4A_mem) (by rw [ev_F4A]; decide)

theorem op_T4A : dInv ⟨(188 : ℤ), (1068242026158857531026326476645811351087800242865804551166333 : ℤ), (1147103706788938432457788429806321957769801073618740481097155 : ℤ)⟩ = ⟨(211 : ℤ), (1125552058983116054691033995833313048385043821593991095637389 : ℤ), (1208644583742909212566608885998860894212412810914710616535669 : ℤ)⟩ := by
  rfl

theorem ev_T4A : (JT4A).value = ⟨(211 : ℤ), (1125552058983116054691033995833313048385043821593991095637389 : ℤ), (1208644583742909212566608885998860894212412810914710616535669 : ℤ)⟩ := by
  rw [show (JT4A).value = dInv (JF4A).value from rfl, ev_F4A]
  exact op_T4A

theorem p0_T4A : (JT4A).part 0 = ⟨(211 : ℤ), (-1479362730012846360499930662975187723016200104635102511974896 : ℤ), (-1213851544908414681282299892458051075685306970796783825367392 : ℤ)⟩ := by
  rw [show (JT4A).part 0 = dNeg (dMul (dMul (dInv (JF4A).value) (dInv (JF4A).value)) ((JF4A).part 0)) from rfl, ev_F4A, op_T4A, p0_F4A]
  rfl

theorem p1_T4A : (JT4A).part 1 = ⟨(211 : ℤ), (-1524894967439968157535460064459071191773907679638475231986530 : ℤ), (-1260888730625399798000766683818764085082574213602474882888785 : ℤ)⟩ := by
  rw [show (JT4A).part 1 = dNeg (dMul (dMul (dInv (JF4A).value) (dInv (JF4A).value)) ((JF4A).part 1)) from rfl, ev_F4A, op_T4A, p1_F4A]
  rfl

theorem p2_T4A : (JT4A).part 2 = ⟨(213 : ℤ), (1045695400060492309891310012389022432785748801028802633682647 : ℤ), (1279664649699760930898350079085611297058978367771308757614339 : ℤ)⟩ := by
  rw [show (JT4A).part 2 = dNeg (dMul (dMul (dInv (JF4A).value) (dInv (JF4A).value)) ((JF4A).part 2)) from rfl, ev_F4A, op_T4A, p2_F4A]
  rfl

def JT4B : DCJet := DCJetKit.inv JF4B
theorem JT4B_mem : JetMem JT4B fT4B D :=
  DCJetKit.inv_mem (JF4B_mem) (by rw [ev_F4B]; decide)

theorem op_T4B : dInv ⟨(188 : ℤ), (780456862036294756893505935969957633628828015937899570535840 : ℤ), (890026016944117035372060496339195962965048175818158551714555 : ℤ)⟩ = ⟨(210 : ℤ), (725329886128779010495040100040419289737041402661416503243496 : ℤ), (827159707248118970254253174975655351276412305791823958119110 : ℤ)⟩ := by
  rfl

theorem ev_T4B : (JT4B).value = ⟨(210 : ℤ), (725329886128779010495040100040419289737041402661416503243496 : ℤ), (827159707248118970254253174975655351276412305791823958119110 : ℤ)⟩ := by
  rw [show (JT4B).value = dInv (JF4B).value from rfl, ev_F4B]
  exact op_T4B

theorem p0_T4B : (JT4B).part 0 = ⟨(212 : ℤ), (813134589536395662865509205452191967008688578321706729644112 : ℤ), (1129267766866133862143285451089778087105025851760264330245441 : ℤ)⟩ := by
  rw [show (JT4B).part 0 = dNeg (dMul (dMul (dInv (JF4B).value) (dInv (JF4B).value)) ((JF4B).part 0)) from rfl, ev_F4B, op_T4B, p0_F4B]
  rfl

theorem p1_T4B : (JT4B).part 1 = ⟨(210 : ℤ), (-1178057545573048608963159612765917879205308617885678398295745 : ℤ), (-818806837171170915460744483906898235604840739259222659059374 : ℤ)⟩ := by
  rw [show (JT4B).part 1 = dNeg (dMul (dMul (dInv (JF4B).value) (dInv (JF4B).value)) ((JF4B).part 1)) from rfl, ev_F4B, op_T4B, p1_F4B]
  rfl

theorem p2_T4B : (JT4B).part 2 = ⟨(210 : ℤ), (-1172125705831150999586297766504475194175931769066258074143061 : ℤ), (-815570394139180346186551541879948998408741455427926556083067 : ℤ)⟩ := by
  rw [show (JT4B).part 2 = dNeg (dMul (dMul (dInv (JF4B).value) (dInv (JF4B).value)) ((JF4B).part 2)) from rfl, ev_F4B, op_T4B, p2_F4B]
  rfl

def JT4C : DCJet := DCJetKit.inv JF4C
theorem JT4C_mem : JetMem JT4C fT4C D :=
  DCJetKit.inv_mem (JF4C_mem) (by rw [ev_F4C]; decide)

theorem op_T4C : dInv ⟨(188 : ℤ), (1109262180022795657754042201966183125088622080845949126062073 : ℤ), (1197755391677966834200174374165690060918509019727089098613763 : ℤ)⟩ = ⟨(211 : ℤ), (1077953769203813494258532399661435945369329512308413602512855 : ℤ), (1163949300982136887529794026238917693775666264733456028387881 : ℤ)⟩ := by
  rfl

theorem ev_T4C : (JT4C).value = ⟨(211 : ℤ), (1077953769203813494258532399661435945369329512308413602512855 : ℤ), (1163949300982136887529794026238917693775666264733456028387881 : ℤ)⟩ := by
  rw [show (JT4C).value = dInv (JF4C).value from rfl, ev_F4C]
  exact op_T4C

theorem p0_T4C : (JT4C).part 0 = ⟨(211 : ℤ), (-1420202743569438528128686178934154290830312372019073446795312 : ℤ), (-1146119402251373190983000726038443145044466415554621898967955 : ℤ)⟩ := by
  rw [show (JT4C).part 0 = dNeg (dMul (dMul (dInv (JF4C).value) (dInv (JF4C).value)) ((JF4C).part 0)) from rfl, ev_F4C, op_T4C, p0_F4C]
  rfl

theorem p1_T4C : (JT4C).part 1 = ⟨(213 : ℤ), (966830876448584096241417323124658070958101328956071318378337 : ℤ), (1196221522668838004421785066163978649990469367095543955308640 : ℤ)⟩ := by
  rw [show (JT4C).part 1 = dNeg (dMul (dMul (dInv (JF4C).value) (dInv (JF4C).value)) ((JF4C).part 1)) from rfl, ev_F4C, op_T4C, p1_F4C]
  rfl

theorem p2_T4C : (JT4C).part 2 = ⟨(211 : ℤ), (-1456539039126668832233085859454261240690652795139524529267451 : ℤ), (-1185821964317679823275640263912026500474597912903552532794635 : ℤ)⟩ := by
  rw [show (JT4C).part 2 = dNeg (dMul (dMul (dInv (JF4C).value) (dInv (JF4C).value)) ((JF4C).part 2)) from rfl, ev_F4C, op_T4C, p2_F4C]
  rfl

def JTA : DCJet := DCJetKit.mul JDlt JT4A
theorem JTA_mem : JetMem JTA fTA D :=
  DCJetKit.mul_mem (JDlt_mem) (JT4A_mem)

theorem op_TA : dMul ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ ⟨(211 : ℤ), (1125552058983116054691033995833313048385043821593991095637389 : ℤ), (1208644583742909212566608885998860894212412810914710616535669 : ℤ)⟩ = ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ := by
  rfl

theorem ev_TA : (JTA).value = ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ := by
  rw [show (JTA).value = dMul (JDlt).value (JT4A).value from rfl, ev_Dlt, ev_T4A]
  exact op_TA

theorem p0_TA : (JTA).part 0 = ⟨(205 : ℤ), (-1544801904090408900984118348273854039951061643558164313597895 : ℤ), (-932530688758517267660005431192462691007188317187251882288845 : ℤ)⟩ := by
  rw [show (JTA).part 0 = dAdd (dMul (JDlt).value ((JT4A).part 0)) (dMul (JT4A).value ((JDlt).part 0)) from rfl, ev_Dlt, ev_T4A, p0_Dlt, p0_T4A]
  rfl

theorem p1_TA : (JTA).part 1 = ⟨(205 : ℤ), (-1256045663250587518913029453616992929121390358867178133622443 : ℤ), (-596980215726809632268397009815347066817446430875646740568039 : ℤ)⟩ := by
  rw [show (JTA).part 1 = dAdd (dMul (JDlt).value ((JT4A).part 1)) (dMul (JT4A).value ((JDlt).part 1)) from rfl, ev_Dlt, ev_T4A, p1_Dlt, p1_T4A]
  rfl

theorem p2_TA : (JTA).part 2 = ⟨(205 : ℤ), (-992495103583563418254857502116615277278800246378041832206825 : ℤ), (-422929052984449181422786283271108646350159483906564233371429 : ℤ)⟩ := by
  rw [show (JTA).part 2 = dAdd (dMul (JDlt).value ((JT4A).part 2)) (dMul (JT4A).value ((JDlt).part 2)) from rfl, ev_Dlt, ev_T4A, p2_Dlt, p2_T4A]
  rfl

def JTB : DCJet := DCJetKit.mul JDlt JT4B
theorem JTB_mem : JetMem JTB fTB D :=
  DCJetKit.mul_mem (JDlt_mem) (JT4B_mem)

theorem op_TB : dMul ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ ⟨(210 : ℤ), (725329886128779010495040100040419289737041402661416503243496 : ℤ), (827159707248118970254253174975655351276412305791823958119110 : ℤ)⟩ = ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ := by
  rfl

theorem ev_TB : (JTB).value = ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ := by
  rw [show (JTB).value = dMul (JDlt).value (JT4B).value from rfl, ev_Dlt, ev_T4B]
  exact op_TB

theorem p0_TB : (JTB).part 0 = ⟨(204 : ℤ), (-856885355464992755554306580006438121149250270097630346363113 : ℤ), (-464674178454667733246817890161574103315535563058057148453894 : ℤ)⟩ := by
  rw [show (JTB).part 0 = dAdd (dMul (JDlt).value ((JT4B).part 0)) (dMul (JT4B).value ((JDlt).part 0)) from rfl, ev_Dlt, ev_T4B, p0_Dlt, p0_T4B]
  rfl

theorem p1_TB : (JTB).part 1 = ⟨(204 : ℤ), (-883214272092349094741761625482198563378747557552024062387977 : ℤ), (-385400942519003864233396083549270821661966074361571435696457 : ℤ)⟩ := by
  rw [show (JTB).part 1 = dAdd (dMul (JDlt).value ((JT4B).part 1)) (dMul (JT4B).value ((JDlt).part 1)) from rfl, ev_Dlt, ev_T4B, p1_Dlt, p1_T4B]
  rfl

theorem p2_TB : (JTB).part 2 = ⟨(204 : ℤ), (-904908112614868364148372656891259588936854906552753878712308 : ℤ), (-399133330038710409620020763455099526522232758046311426426574 : ℤ)⟩ := by
  rw [show (JTB).part 2 = dAdd (dMul (JDlt).value ((JT4B).part 2)) (dMul (JT4B).value ((JDlt).part 2)) from rfl, ev_Dlt, ev_T4B, p2_Dlt, p2_T4B]
  rfl

def JTC : DCJet := DCJetKit.mul JDlt JT4C
theorem JTC_mem : JetMem JTC fTC D :=
  DCJetKit.mul_mem (JDlt_mem) (JT4C_mem)

theorem op_TC : dMul ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ ⟨(211 : ℤ), (1077953769203813494258532399661435945369329512308413602512855 : ℤ), (1163949300982136887529794026238917693775666264733456028387881 : ℤ)⟩ = ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ := by
  rfl

theorem ev_TC : (JTC).value = ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ := by
  rw [show (JTC).value = dMul (JDlt).value (JT4C).value from rfl, ev_Dlt, ev_T4C]
  exact op_TC

theorem p0_TC : (JTC).part 0 = ⟨(205 : ℤ), (-1486893491026208448083744339228768557186663139379541321331457 : ℤ), (-891277595107969453131081316746643549343371284169981038808428 : ℤ)⟩ := by
  rw [show (JTC).part 0 = dAdd (dMul (JDlt).value ((JT4C).part 0)) (dMul (JT4C).value ((JDlt).part 0)) from rfl, ev_Dlt, ev_T4C, p0_Dlt, p0_T4C]
  rfl

theorem p1_TC : (JTC).part 1 = ⟨(205 : ℤ), (-924913888297785683070572448495817101602404131162758885514096 : ℤ), (-385389978162868352324689174281258362985292277554065499441966 : ℤ)⟩ := by
  rw [show (JTC).part 1 = dAdd (dMul (JDlt).value ((JT4C).part 1)) (dMul (JT4C).value ((JDlt).part 1)) from rfl, ev_Dlt, ev_T4C, p1_Dlt, p1_T4C]
  rfl

theorem p2_TC : (JTC).part 2 = ⟨(205 : ℤ), (-1239488775172317836433851212129030362561430340062258231335477 : ℤ), (-590266281983860475547501250592032350102398499676315707556206 : ℤ)⟩ := by
  rw [show (JTC).part 2 = dAdd (dMul (JDlt).value ((JT4C).part 2)) (dMul (JT4C).value ((JDlt).part 2)) from rfl, ev_Dlt, ev_T4C, p2_Dlt, p2_T4C]
  rfl

def JInvA2A : DCJet := DCJetKit.inv JD4Asq
theorem JInvA2A_mem : JetMem JInvA2A fInvA2A D :=
  DCJetKit.inv_mem (JD4Asq_mem) (by rw [ev_D4Asq]; decide)

theorem op_InvA2A : dInv ⟨(189 : ℤ), (820052399215115512916807310144445507363799132612851946717071 : ℤ), (1034717085370539865198315855805099518773257762560806878561085 : ℤ)⟩ = ⟨(210 : ℤ), (1247804793501687347561321076923102450806283522580545772714395 : ℤ), (1574441999412731913203666058312366883568513626250464241628208 : ℤ)⟩ := by
  rfl

theorem ev_InvA2A : (JInvA2A).value = ⟨(210 : ℤ), (1247804793501687347561321076923102450806283522580545772714395 : ℤ), (1574441999412731913203666058312366883568513626250464241628208 : ℤ)⟩ := by
  rw [show (JInvA2A).value = dInv (JD4Asq).value from rfl, ev_D4Asq]
  exact op_InvA2A

theorem p0_InvA2A : (JInvA2A).part 0 = ⟨(209 : ℤ), (-1489385865412982568195484277430827648936676161232672820962954 : ℤ), (-798554620820526329777978626385222026937024298742801322756208 : ℤ)⟩ := by
  rw [show (JInvA2A).part 0 = dNeg (dMul (dMul (dInv (JD4Asq).value) (dInv (JD4Asq).value)) ((JD4Asq).part 0)) from rfl, ev_D4Asq, op_InvA2A, p0_D4Asq]
  rfl

theorem p1_InvA2A : (JInvA2A).part 1 = ⟨(210 : ℤ), (-839483548581952257921946426391790613920202759099021140698108 : ℤ), (-201877703390012816551727724809685152401097007239516995396425 : ℤ)⟩ := by
  rw [show (JInvA2A).part 1 = dNeg (dMul (dMul (dInv (JD4Asq).value) (dInv (JD4Asq).value)) ((JD4Asq).part 1)) from rfl, ev_D4Asq, op_InvA2A, p1_D4Asq]
  rfl

theorem p2_InvA2A : (JInvA2A).part 2 = ⟨(209 : ℤ), (-1392573078739560915069100713197173086394678940164888032529681 : ℤ), (-729049434606628386183310601480459599118731811370106458218671 : ℤ)⟩ := by
  rw [show (JInvA2A).part 2 = dNeg (dMul (dMul (dInv (JD4Asq).value) (dInv (JD4Asq).value)) ((JD4Asq).part 2)) from rfl, ev_D4Asq, op_InvA2A, p2_D4Asq]
  rfl

def JInvA2B : DCJet := DCJetKit.inv JD4Bsq
theorem JInvA2B_mem : JetMem JInvA2B fInvA2B D :=
  DCJetKit.inv_mem (JD4Bsq_mem) (by rw [ev_D4Bsq]; decide)

theorem op_InvA2B : dInv ⟨(189 : ℤ), (785666069346136049431761655017997718441333017629462719091635 : ℤ), (1008970408157009751519757639418847141038449364469856854210572 : ℤ)⟩ = ⟨(209 : ℤ), (639822996098482898003813538612099803624436258777121277278516 : ℤ), (821675384376712437546415534986325918928958686877769619636821 : ℤ)⟩ := by
  rfl

theorem ev_InvA2B : (JInvA2B).value = ⟨(209 : ℤ), (639822996098482898003813538612099803624436258777121277278516 : ℤ), (821675384376712437546415534986325918928958686877769619636821 : ℤ)⟩ := by
  rw [show (JInvA2B).value = dInv (JD4Bsq).value from rfl, ev_D4Bsq]
  exact op_InvA2B

theorem p0_InvA2B : (JInvA2B).part 0 = ⟨(208 : ℤ), (-823358998218610085781549098059254901343930995828445303544862 : ℤ), (-420021308901468309756188311401925899955952553820631917720037 : ℤ)⟩ := by
  rw [show (JInvA2B).part 0 = dNeg (dMul (dMul (dInv (JD4Bsq).value) (dInv (JD4Bsq).value)) ((JD4Bsq).part 0)) from rfl, ev_D4Bsq, op_InvA2B, p0_D4Bsq]
  rfl

theorem p1_InvA2B : (JInvA2B).part 1 = ⟨(209 : ℤ), (-1518769283684709619174614185698864876415574654366266526930244 : ℤ), (-758660745513712436463997936239910956958838416784989340681195 : ℤ)⟩ := by
  rw [show (JInvA2B).part 1 = dNeg (dMul (dMul (dInv (JD4Bsq).value) (dInv (JD4Bsq).value)) ((JD4Bsq).part 1)) from rfl, ev_D4Bsq, op_InvA2B, p1_D4Bsq]
  rfl

theorem p2_InvA2B : (JInvA2B).part 2 = ⟨(211 : ℤ), (-1432114581190765328551534424276963638946652444508644996726175 : ℤ), (-169612373482624069379599627339718581720528062389266175032287 : ℤ)⟩ := by
  rw [show (JInvA2B).part 2 = dNeg (dMul (dMul (dInv (JD4Bsq).value) (dInv (JD4Bsq).value)) ((JD4Bsq).part 2)) from rfl, ev_D4Bsq, op_InvA2B, p2_D4Bsq]
  rfl

def JInvA2C : DCJet := DCJetKit.inv JD4Csq
theorem JInvA2C_mem : JetMem JInvA2C fInvA2C D :=
  DCJetKit.inv_mem (JD4Csq_mem) (by rw [ev_D4Csq]; decide)

theorem op_InvA2C : dInv ⟨(190 : ℤ), (1075382654467573562147347938397195010863241032107569368443737 : ℤ), (1340948681997891370560080266616017535051408574711033464210594 : ℤ)⟩ = ⟨(209 : ℤ), (962844407378659533886189610692397354718305319192678104506340 : ℤ), (1200619085382863681836366251722478176587222009391627905068212 : ℤ)⟩ := by
  rfl

theorem ev_InvA2C : (JInvA2C).value = ⟨(209 : ℤ), (962844407378659533886189610692397354718305319192678104506340 : ℤ), (1200619085382863681836366251722478176587222009391627905068212 : ℤ)⟩ := by
  rw [show (JInvA2C).value = dInv (JD4Csq).value from rfl, ev_D4Csq]
  exact op_InvA2C

theorem p0_InvA2C : (JInvA2C).part 0 = ⟨(209 : ℤ), (519505194439778432761368842158430641430318416879931894802280 : ℤ), (1150295132953225633276524175042474347162309791633771466845696 : ℤ)⟩ := by
  rw [show (JInvA2C).part 0 = dNeg (dMul (dMul (dInv (JD4Csq).value) (dInv (JD4Csq).value)) ((JD4Csq).part 0)) from rfl, ev_D4Csq, op_InvA2C, p0_D4Csq]
  rfl

theorem p1_InvA2C : (JInvA2C).part 1 = ⟨(208 : ℤ), (-1511826918858671173776120230973340135153394160910916579362398 : ℤ), (-852614998087105397685187734859787165863575879439101725664642 : ℤ)⟩ := by
  rw [show (JInvA2C).part 1 = dNeg (dMul (dMul (dInv (JD4Csq).value) (dInv (JD4Csq).value)) ((JD4Csq).part 1)) from rfl, ev_D4Csq, op_InvA2C, p1_D4Csq]
  rfl

theorem p2_InvA2C : (JInvA2C).part 2 = ⟨(208 : ℤ), (-1532640394387143776102711593731711387538352590679471286495110 : ℤ), (-861904254634337050437102314596650958760092277094620661077174 : ℤ)⟩ := by
  rw [show (JInvA2C).part 2 = dNeg (dMul (dMul (dInv (JD4Csq).value) (dInv (JD4Csq).value)) ((JD4Csq).part 2)) from rfl, ev_D4Csq, op_InvA2C, p2_D4Csq]
  rfl

def JKDltA : DCJet := DCJetKit.mul JKA JDlt
theorem JKDltA_mem : JetMem JKDltA fKDltA D :=
  DCJetKit.mul_mem (JKA_mem) (JDlt_mem)

theorem op_KDltA : dMul ⟨(195 : ℤ), (1040405920714448888839011846650123345630352450083414978914842 : ℤ), (1085064048337435062926876982216450883037826536041286247665136 : ℤ)⟩ ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ = ⟨(192 : ℤ), (922398000555943661861322856092945320576796868686935761191684 : ℤ), (1524461465845193729385481255344433808016471268713885697991667 : ℤ)⟩ := by
  rfl

theorem ev_KDltA : (JKDltA).value = ⟨(192 : ℤ), (922398000555943661861322856092945320576796868686935761191684 : ℤ), (1524461465845193729385481255344433808016471268713885697991667 : ℤ)⟩ := by
  rw [show (JKDltA).value = dMul (JKA).value (JDlt).value from rfl, ev_KA, ev_Dlt]
  exact op_KDltA

theorem p0_KDltA : (JKDltA).part 0 = ⟨(189 : ℤ), (-1153610492445050645990690551714232794953786741318229110292367 : ℤ), (-737641287629975812156765967657721669575256829961828672825434 : ℤ)⟩ := by
  rw [show (JKDltA).part 0 = dAdd (dMul (JKA).value ((JDlt).part 0)) (dMul (JDlt).value ((JKA).part 0)) from rfl, ev_KA, ev_Dlt, p0_KA, p0_Dlt]
  rfl

theorem p1_KDltA : (JKDltA).part 1 = ⟨(190 : ℤ), (-1571752481177917068641690579553407965614367897698756799653444 : ℤ), (-517358161069150743097682893502366148964015897203061705822814 : ℤ)⟩ := by
  rw [show (JKDltA).part 1 = dAdd (dMul (JKA).value ((JDlt).part 1)) (dMul (JDlt).value ((JKA).part 1)) from rfl, ev_KA, ev_Dlt, p1_KA, p1_Dlt]
  rfl

theorem p2_KDltA : (JKDltA).part 2 = ⟨(189 : ℤ), (-917024480813439682241610752603175355363803616429314184253974 : ℤ), (-442868304838318772038329040837140801858796095899935244432277 : ℤ)⟩ := by
  rw [show (JKDltA).part 2 = dAdd (dMul (JKA).value ((JDlt).part 2)) (dMul (JDlt).value ((JKA).part 2)) from rfl, ev_KA, ev_Dlt, p2_KA, p2_Dlt]
  rfl

def JKDltB : DCJet := DCJetKit.mul JKB JDlt
theorem JKDltB_mem : JetMem JKDltB fKDltB D :=
  DCJetKit.mul_mem (JKB_mem) (JDlt_mem)

theorem op_KDltB : dMul ⟨(195 : ℤ), (1063199902802517431467791124890635681448028083127857000006579 : ℤ), (1115146078936933578663128627404557119870685376588838910686760 : ℤ)⟩ ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ = ⟨(192 : ℤ), (942606577885361800731700431093671078432864885645838553557864 : ℤ), (1566725235005712631388843321515980056520046432973472122576445 : ℤ)⟩ := by
  rfl

theorem ev_KDltB : (JKDltB).value = ⟨(192 : ℤ), (942606577885361800731700431093671078432864885645838553557864 : ℤ), (1566725235005712631388843321515980056520046432973472122576445 : ℤ)⟩ := by
  rw [show (JKDltB).value = dMul (JKB).value (JDlt).value from rfl, ev_KB, ev_Dlt]
  exact op_KDltB

theorem p0_KDltB : (JKDltB).part 0 = ⟨(189 : ℤ), (-1185592886651924767435212674720902988972071835340725428385879 : ℤ), (-753802078301093317494860445362017361724373334673784880795996 : ℤ)⟩ := by
  rw [show (JKDltB).part 0 = dAdd (dMul (JKB).value ((JDlt).part 0)) (dMul (JDlt).value ((JKB).part 0)) from rfl, ev_KB, ev_Dlt, p0_KB, p0_Dlt]
  rfl

theorem p1_KDltB : (JKDltB).part 1 = ⟨(189 : ℤ), (-911796555319169558015809516869024855444882848870506557044824 : ℤ), (-431916100212503898708413174449380683623461231899246996779699 : ℤ)⟩ := by
  rw [show (JKDltB).part 1 = dAdd (dMul (JKB).value ((JDlt).part 1)) (dMul (JDlt).value ((JKB).part 1)) from rfl, ev_KB, ev_Dlt, p1_KB, p1_Dlt]
  rfl

theorem p2_KDltB : (JKDltB).part 2 = ⟨(189 : ℤ), (-840020088202590531079721137922589489707492301223349379273983 : ℤ), (-286336346439825645192263315854076539873234917409146278233377 : ℤ)⟩ := by
  rw [show (JKDltB).part 2 = dAdd (dMul (JKB).value ((JDlt).part 2)) (dMul (JDlt).value ((JKB).part 2)) from rfl, ev_KB, ev_Dlt, p2_KB, p2_Dlt]
  rfl

def JKDltC : DCJet := DCJetKit.mul JKC JDlt
theorem JKDltC_mem : JetMem JKDltC fKDltC D :=
  DCJetKit.mul_mem (JKC_mem) (JDlt_mem)

theorem op_KDltC : dMul ⟨(195 : ℤ), (1275587419532786480725209508900414873882124736464780952662231 : ℤ), (1275587419533414191220135863051932871839335252872317519068917 : ℤ)⟩ ⟨(200 : ℤ), (11397370272740595839809771867756869589328801928213285408180684 : ℤ), (18061349504497839836771016887493827171430585322027857889667964 : ℤ)⟩ = ⟨(191 : ℤ), (565452032656342811102562306789087692500575185663481622313363 : ℤ), (896068702292340030043206152677389645301654434110414262655014 : ℤ)⟩ := by
  rfl

theorem ev_KDltC : (JKDltC).value = ⟨(191 : ℤ), (565452032656342811102562306789087692500575185663481622313363 : ℤ), (896068702292340030043206152677389645301654434110414262655014 : ℤ)⟩ := by
  rw [show (JKDltC).value = dMul (JKC).value (JDlt).value from rfl, ev_KC, ev_Dlt]
  exact op_KDltC

theorem p0_KDltC : (JKDltC).part 0 = ⟨(189 : ℤ), (-1243976879038867525938905478708241801755607398378625198731833 : ℤ), (-726592089500479303610981578318561883889030586074194790640104 : ℤ)⟩ := by
  rw [show (JKDltC).part 0 = dAdd (dMul (JKC).value ((JDlt).part 0)) (dMul (JDlt).value ((JKC).part 0)) from rfl, ev_KC, ev_Dlt, p0_KC, p0_Dlt]
  rfl

theorem p1_KDltC : (JKDltC).part 1 = ⟨(189 : ℤ), (-1042981038186309689249477474292245357174116027645201218294439 : ℤ), (-518196758927908861594232429960852802775572370565841043963489 : ℤ)⟩ := by
  rw [show (JKDltC).part 1 = dAdd (dMul (JKC).value ((JDlt).part 1)) (dMul (JDlt).value ((JKC).part 1)) from rfl, ev_KC, ev_Dlt, p1_KC, p1_Dlt]
  rfl

theorem p2_KDltC : (JKDltC).part 2 = ⟨(189 : ℤ), (-1078042252825627820566103920021378143260872613966401799232596 : ℤ), (-542977723323258934542135141974926195893759887344458454849075 : ℤ)⟩ := by
  rw [show (JKDltC).part 2 = dAdd (dMul (JKC).value ((JDlt).part 2)) (dMul (JDlt).value ((JKC).part 2)) from rfl, ev_KC, ev_Dlt, p2_KC, p2_Dlt]
  rfl

def JGA : DCJet := DCJetKit.mul JKDltA JInvA2A
theorem JGA_mem : JetMem JGA fGA D :=
  DCJetKit.mul_mem (JKDltA_mem) (JInvA2A_mem)

theorem op_GA : dMul ⟨(192 : ℤ), (922398000555943661861322856092945320576796868686935761191684 : ℤ), (1524461465845193729385481255344433808016471268713885697991667 : ℤ)⟩ ⟨(210 : ℤ), (1247804793501687347561321076923102450806283522580545772714395 : ℤ), (1574441999412731913203666058312366883568513626250464241628208 : ℤ)⟩ = ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ := by
  rfl

theorem ev_GA : (JGA).value = ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ := by
  rw [show (JGA).value = dMul (JKDltA).value (JInvA2A).value from rfl, ev_KDltA, ev_InvA2A]
  exact op_GA

theorem p0_GA : (JGA).part 0 = ⟨(199 : ℤ), (-1483517462720312671513637961809045356600259412760174705247744 : ℤ), (-687380969621443942619712700260933779152247154684309081725632 : ℤ)⟩ := by
  rw [show (JGA).part 0 = dAdd (dMul (JKDltA).value ((JInvA2A).part 0)) (dMul (JInvA2A).value ((JKDltA).part 0)) from rfl, ev_KDltA, ev_InvA2A, p0_KDltA, p0_InvA2A]
  rfl

theorem p1_GA : (JGA).part 1 = ⟨(199 : ℤ), (-869533585718418185525601720260475592329786180303440762205223 : ℤ), (-215352076983591402120627299144918116303853425274380394010941 : ℤ)⟩ := by
  rw [show (JGA).part 1 = dAdd (dMul (JKDltA).value ((JInvA2A).part 1)) (dMul (JInvA2A).value ((JKDltA).part 1)) from rfl, ev_KDltA, ev_InvA2A, p1_KDltA, p1_InvA2A]
  rfl

theorem p2_GA : (JGA).part 2 = ⟨(199 : ℤ), (-1228754813145779996942540144542461016172704070792458914985280 : ℤ), (-448512393765916177517021176380170197721981920162036696789005 : ℤ)⟩ := by
  rw [show (JGA).part 2 = dAdd (dMul (JKDltA).value ((JInvA2A).part 2)) (dMul (JInvA2A).value ((JKDltA).part 2)) from rfl, ev_KDltA, ev_InvA2A, p2_KDltA, p2_InvA2A]
  rfl

def JGB : DCJet := DCJetKit.mul JKDltB JInvA2B
theorem JGB_mem : JetMem JGB fGB D :=
  DCJetKit.mul_mem (JKDltB_mem) (JInvA2B_mem)

theorem op_GB : dMul ⟨(192 : ℤ), (942606577885361800731700431093671078432864885645838553557864 : ℤ), (1566725235005712631388843321515980056520046432973472122576445 : ℤ)⟩ ⟨(209 : ℤ), (639822996098482898003813538612099803624436258777121277278516 : ℤ), (821675384376712437546415534986325918928958686877769619636821 : ℤ)⟩ = ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ := by
  rfl

theorem ev_GB : (JGB).value = ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ := by
  rw [show (JGB).value = dMul (JKDltB).value (JInvA2B).value from rfl, ev_KDltB, ev_InvA2B]
  exact op_GB

theorem p0_GB : (JGB).part 0 = ⟨(198 : ℤ), (-806917743643613990349377369230183838317516948663081834209738 : ℤ), (-361730571029918253299208580132547316828655871585267013671055 : ℤ)⟩ := by
  rw [show (JGB).part 0 = dAdd (dMul (JKDltB).value ((JInvA2B).part 0)) (dMul (JInvA2B).value ((JKDltB).part 0)) from rfl, ev_KDltB, ev_InvA2B, p0_KDltB, p0_InvA2B]
  rfl

theorem p1_GB : (JGB).part 1 = ⟨(199 : ℤ), (-1302648299562073763637706428020123059559743643739816039729847 : ℤ), (-455200722574056226469947926924758707284907843036659687872860 : ℤ)⟩ := by
  rw [show (JGB).part 1 = dAdd (dMul (JKDltB).value ((JInvA2B).part 1)) (dMul (JInvA2B).value ((JKDltB).part 1)) from rfl, ev_KDltB, ev_InvA2B, p1_KDltB, p1_InvA2B]
  rfl

theorem p2_GB : (JGB).part 2 = ⟨(199 : ℤ), (-946321976450549032605489052229753359094025520892079576478341 : ℤ), (-234235238981526694336174798451766389432838405359726060001122 : ℤ)⟩ := by
  rw [show (JGB).part 2 = dAdd (dMul (JKDltB).value ((JInvA2B).part 2)) (dMul (JInvA2B).value ((JKDltB).part 2)) from rfl, ev_KDltB, ev_InvA2B, p2_KDltB, p2_InvA2B]
  rfl

def JGC : DCJet := DCJetKit.mul JKDltC JInvA2C
theorem JGC_mem : JetMem JGC fGC D :=
  DCJetKit.mul_mem (JKDltC_mem) (JInvA2C_mem)

theorem op_GC : dMul ⟨(191 : ℤ), (565452032656342811102562306789087692500575185663481622313363 : ℤ), (896068702292340030043206152677389645301654434110414262655014 : ℤ)⟩ ⟨(209 : ℤ), (962844407378659533886189610692397354718305319192678104506340 : ℤ), (1200619085382863681836366251722478176587222009391627905068212 : ℤ)⟩ = ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ := by
  rfl

theorem ev_GC : (JGC).value = ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ := by
  rw [show (JGC).value = dMul (JKDltC).value (JInvA2C).value from rfl, ev_KDltC, ev_InvA2C]
  exact op_GC

theorem p0_GC : (JGC).part 0 = ⟨(198 : ℤ), (-883732618553476037461100254454325238512974123410310051441217 : ℤ), (-275000809545984275287855940225865553820580697163060673589825 : ℤ)⟩ := by
  rw [show (JGC).part 0 = dAdd (dMul (JKDltC).value ((JInvA2C).part 0)) (dMul (JInvA2C).value ((JKDltC).part 0)) from rfl, ev_KDltC, ev_InvA2C, p0_KDltC, p0_InvA2C]
  rfl

theorem p1_GC : (JGC).part 1 = ⟨(198 : ℤ), (-1200776432961273212140568252635353765048487344636938682132323 : ℤ), (-460502690673143077580559596941441516217941869372357601599776 : ℤ)⟩ := by
  rw [show (JGC).part 1 = dAdd (dMul (JKDltC).value ((JInvA2C).part 1)) (dMul (JInvA2C).value ((JKDltC).part 1)) from rfl, ev_KDltC, ev_InvA2C, p1_KDltC, p1_InvA2C]
  rfl

theorem p2_GC : (JGC).part 2 = ⟨(198 : ℤ), (-1232775373828889450800427568709894206465982066863899161221901 : ℤ), (-476985297187058468806875388443055966625503892622096896723708 : ℤ)⟩ := by
  rw [show (JGC).part 2 = dAdd (dMul (JKDltC).value ((JInvA2C).part 2)) (dMul (JInvA2C).value ((JKDltC).part 2)) from rfl, ev_KDltC, ev_InvA2C, p2_KDltC, p2_InvA2C]
  rfl

def JInvD4A : DCJet := DCJetKit.inv JD4A
theorem JInvD4A_mem : JetMem JInvD4A fInvD4A D :=
  DCJetKit.inv_mem (JD4A_mem) (by rw [ev_D4A]; decide)

theorem op_InvD4A : dInv ⟨(194 : ℤ), (811718362051959021221070227209858817434547300696546197227828 : ℤ), (911791162911414164264663553772158721208345175519987873310647 : ℤ)⟩ = ⟨(205 : ℤ), (1416031424258160552026942061213876800307553066984693798063993 : ℤ), (1590607037371427492752460293552287084972755165387525452792960 : ℤ)⟩ := by
  rfl

theorem ev_InvD4A : (JInvD4A).value = ⟨(205 : ℤ), (1416031424258160552026942061213876800307553066984693798063993 : ℤ), (1590607037371427492752460293552287084972755165387525452792960 : ℤ)⟩ := by
  rw [show (JInvD4A).value = dInv (JD4A).value from rfl, ev_D4A]
  exact op_InvD4A

theorem p0_InvD4A : (JInvD4A).part 0 = ⟨(205 : ℤ), (-1339533110179596185912649290779198814482098910867803655825713 : ℤ), (-1017936945119519947896376728459531287237648248471581627329323 : ℤ)⟩ := by
  rw [show (JInvD4A).part 0 = dNeg (dMul (dMul (dInv (JD4A).value) (dInv (JD4A).value)) ((JD4A).part 0)) from rfl, ev_D4A, op_InvD4A, p0_D4A]
  rfl

theorem p1_InvD4A : (JInvD4A).part 1 = ⟨(207 : ℤ), (-1510039855876806743440754473757770586874992056355019441022180 : ℤ), (-514676810624228222135785307402766913707823477528442266047163 : ℤ)⟩ := by
  rw [show (JInvD4A).part 1 = dNeg (dMul (dMul (dInv (JD4A).value) (dInv (JD4A).value)) ((JD4A).part 1)) from rfl, ev_D4A, op_InvD4A, p1_D4A]
  rfl

theorem p2_InvD4A : (JInvD4A).part 2 = ⟨(205 : ℤ), (-1252461024799060487630554223254626964245430873791807152399402 : ℤ), (-929336998315830982562988917645769790969293921130856078211678 : ℤ)⟩ := by
  rw [show (JInvD4A).part 2 = dNeg (dMul (dMul (dInv (JD4A).value) (dInv (JD4A).value)) ((JD4A).part 2)) from rfl, ev_D4A, op_InvD4A, p2_D4A]
  rfl

def JInvD4B : DCJet := DCJetKit.inv JD4B
theorem JInvD4B_mem : JetMem JInvD4B fInvD4B D :=
  DCJetKit.inv_mem (JD4B_mem) (by rw [ev_D4B]; decide)

theorem op_InvD4B : dInv ⟨(194 : ℤ), (794517682910748089668306555125200761408368760420833179199617 : ℤ), (900375736678588096163830783243737965166197690220787624436542 : ℤ)⟩ = ⟨(204 : ℤ), (716992299129643258382373053186858070659404380172097447504591 : ℤ), (812521210549628783580584286488869997300344157056145111545713 : ℤ)⟩ := by
  rfl

theorem ev_InvD4B : (JInvD4B).value = ⟨(204 : ℤ), (716992299129643258382373053186858070659404380172097447504591 : ℤ), (812521210549628783580584286488869997300344157056145111545713 : ℤ)⟩ := by
  rw [show (JInvD4B).value = dInv (JD4B).value from rfl, ev_D4B]
  exact op_InvD4B

theorem p0_InvD4B : (JInvD4B).part 0 = ⟨(205 : ℤ), (-1436922834410207283459815561436302727950346757622054355972615 : ℤ), (-1066783233632730045589597804685417308204849130348104940295312 : ℤ)⟩ := by
  rw [show (JInvD4B).part 0 = dNeg (dMul (dMul (dInv (JD4B).value) (dInv (JD4B).value)) ((JD4B).part 0)) from rfl, ev_D4B, op_InvD4B, p0_D4B]
  rfl

theorem p1_InvD4B : (JInvD4B).part 1 = ⟨(205 : ℤ), (-1325275043236945440378616232599113165265656090687827106996372 : ℤ), (-963435123620351401314781992696617810062733295800053392788729 : ℤ)⟩ := by
  rw [show (JInvD4B).part 1 = dNeg (dMul (dMul (dInv (JD4B).value) (dInv (JD4B).value)) ((JD4B).part 1)) from rfl, ev_D4B, op_InvD4B, p1_D4B]
  rfl

theorem p2_InvD4B : (JInvD4B).part 2 = ⟨(207 : ℤ), (-1249660322931483127908300051283591583925029157783523989838746 : ℤ), (-215393400779056867511039361250741190926871102001540632227116 : ℤ)⟩ := by
  rw [show (JInvD4B).part 2 = dNeg (dMul (dMul (dInv (JD4B).value) (dInv (JD4B).value)) ((JD4B).part 2)) from rfl, ev_D4B, op_InvD4B, p2_D4B]
  rfl

def JInvD4C : DCJet := DCJetKit.inv JD4C
theorem JInvD4C_mem : JetMem JInvD4C fInvD4C D :=
  DCJetKit.inv_mem (JD4C_mem) (by rw [ev_D4C]; decide)

theorem op_InvD4C : dInv ⟨(195 : ℤ), (1314562018164287360137992701436860404057508287066124100461832 : ℤ), (1467931010811258200449222572531530043333023059084882674361223 : ℤ)⟩ = ⟨(204 : ℤ), (879554236223886780586152194374509245039384312461527462552798 : ℤ), (982171187972126533137383487664930032701012744908221515451680 : ℤ)⟩ := by
  rfl

theorem ev_InvD4C : (JInvD4C).value = ⟨(204 : ℤ), (879554236223886780586152194374509245039384312461527462552798 : ℤ), (982171187972126533137383487664930032701012744908221515451680 : ℤ)⟩ := by
  rw [show (JInvD4C).value = dInv (JD4C).value from rfl, ev_D4C]
  exact op_InvD4C

theorem p0_InvD4C : (JInvD4C).part 0 = ⟨(205 : ℤ), (529933008978826192391237709323057876938719580636165168006377 : ℤ), (842687717873561994351947175495580912780071379725476893542822 : ℤ)⟩ := by
  rw [show (JInvD4C).part 0 = dNeg (dMul (dMul (dInv (JD4C).value) (dInv (JD4C).value)) ((JD4C).part 0)) from rfl, ev_D4C, op_InvD4C, p0_D4C]
  rfl

theorem p1_InvD4C : (JInvD4C).part 1 = ⟨(204 : ℤ), (-1107540090865217006709990689923786932159994560875700842737715 : ℤ), (-869729188991107107006683982849395862988436806112727876541038 : ℤ)⟩ := by
  rw [show (JInvD4C).part 1 = dNeg (dMul (dMul (dInv (JD4C).value) (dInv (JD4C).value)) ((JD4C).part 1)) from rfl, ev_D4C, op_InvD4C, p1_D4C]
  rfl

theorem p2_InvD4C : (JInvD4C).part 2 = ⟨(204 : ℤ), (-1122787708360629816212055985353423138744605166057405726077661 : ℤ), (-879204904972271129610118309545148169924381387740513524850665 : ℤ)⟩ := by
  rw [show (JInvD4C).part 2 = dNeg (dMul (dMul (dInv (JD4C).value) (dInv (JD4C).value)) ((JD4C).part 2)) from rfl, ev_D4C, op_InvD4C, p2_D4C]
  rfl

def JIA : DCJet := DCJetKit.inv JA
theorem JIA_mem : JetMem JIA fIA D :=
  DCJetKit.inv_mem (JA_mem) (by rw [ev_A]; decide)

theorem op_IA : dInv ⟨(195 : ℤ), (1310190349648086688609276427437736092310671362412139342631099 : ℤ), (1357690902654081626216419595205048512860410608729347869873497 : ℤ)⟩ = ⟨(204 : ℤ), (950971194194127044127820492995137417411365456285590905643958 : ℤ), (985448365873131863982169256768428950053449540701194478328512 : ℤ)⟩ := by
  rfl

theorem ev_IA : (JIA).value = ⟨(204 : ℤ), (950971194194127044127820492995137417411365456285590905643958 : ℤ), (985448365873131863982169256768428950053449540701194478328512 : ℤ)⟩ := by
  rw [show (JIA).value = dInv (JA).value from rfl, ev_A]
  exact op_IA

theorem p0_IA : (JIA).part 0 = ⟨(205 : ℤ), (-1163974389931860684375774620761054132074770475276950882151013 : ℤ), (-1062756726173353578180967228423458019307595001416205213925767 : ℤ)⟩ := by
  rw [show (JIA).part 0 = dNeg (dMul (dMul (dInv (JA).value) (dInv (JA).value)) ((JA).part 0)) from rfl, ev_A, op_IA, p0_A]
  rfl

theorem p1_IA : (JIA).part 1 = ⟨(205 : ℤ), (-1199799517337231039461984606842326349716194936311137747025331 : ℤ), (-1103938933100282863617555589090467919902593784800108859099385 : ℤ)⟩ := by
  rw [show (JIA).part 1 = dNeg (dMul (dMul (dInv (JA).value) (dInv (JA).value)) ((JA).part 1)) from rfl, ev_A, op_IA, p1_A]
  rfl

theorem p2_IA : (JIA).part 2 = ⟨(207 : ℤ), (915531907179533498893715053212291345969734108949195257163444 : ℤ), (1006850348283894563631224990139253054872729072881444024651193 : ℤ)⟩ := by
  rw [show (JIA).part 2 = dNeg (dMul (dMul (dInv (JA).value) (dInv (JA).value)) ((JA).part 2)) from rfl, ev_A, op_IA, p2_A]
  rfl

def JIB : DCJet := DCJetKit.inv JB
theorem JIB_mem : JetMem JIB fIB D :=
  DCJetKit.inv_mem (JB_mem) (by rw [ev_B]; decide)

theorem op_IB : dInv ⟨(195 : ℤ), (1119886522603568120731881860118615247481823501238675430013657 : ℤ), (1195916663905892051976153956058604262341990085187101712960850 : ℤ)⟩ = ⟨(204 : ℤ), (1079611128443189150836564483201376003437953269838744337469864 : ℤ), (1152906935643606595975083348888388424918997760052031395927874 : ℤ)⟩ := by
  rfl

theorem ev_IB : (JIB).value = ⟨(204 : ℤ), (1079611128443189150836564483201376003437953269838744337469864 : ℤ), (1152906935643606595975083348888388424918997760052031395927874 : ℤ)⟩ := by
  rw [show (JIB).value = dInv (JB).value from rfl, ev_B]
  exact op_IB

theorem p0_IB : (JIB).part 0 = ⟨(207 : ℤ), (1292471916318893449520027643815206703446445884511479094478525 : ℤ), (1473923400061312065718348450306891790988203344359220231599884 : ℤ)⟩ := by
  rw [show (JIB).part 0 = dNeg (dMul (dMul (dInv (JB).value) (dInv (JB).value)) ((JB).part 0)) from rfl, ev_B, op_IB, p0_B]
  rfl

theorem p1_IB : (JIB).part 1 = ⟨(205 : ℤ), (-1537603953628780939576681848143363838852993137401547616982016 : ℤ), (-1301487915471669791105448351926308966769634766691471823639997 : ℤ)⟩ := by
  rw [show (JIB).part 1 = dNeg (dMul (dMul (dInv (JB).value) (dInv (JB).value)) ((JB).part 1)) from rfl, ev_B, op_IB, p1_B]
  rfl

theorem p2_IB : (JIB).part 2 = ⟨(205 : ℤ), (-1529861700057460360303828067735032832134188995183792702269020 : ℤ), (-1296343611218177509329743985759168704751113605406531617202614 : ℤ)⟩ := by
  rw [show (JIB).part 2 = dNeg (dMul (dMul (dInv (JB).value) (dInv (JB).value)) ((JB).part 2)) from rfl, ev_B, op_IB, p2_B]
  rfl

def JIC : DCJet := DCJetKit.inv JC
theorem JIC_mem : JetMem JIC fIC D :=
  DCJetKit.inv_mem (JC_mem) (by rw [ev_C]; decide)

theorem op_IC : dInv ⟨(195 : ℤ), (1335108833817039519080090543859417568596208511869928248159277 : ℤ), (1387342317744129399973935671924094705106485942740566760057855 : ℤ)⟩ = ⟨(204 : ℤ), (930646259780262330129504379471157488711068087944508642585160 : ℤ), (967055948054933861789239919713877404474162541868495935751340 : ℤ)⟩ := by
  rfl

theorem ev_IC : (JIC).value = ⟨(204 : ℤ), (930646259780262330129504379471157488711068087944508642585160 : ℤ), (967055948054933861789239919713877404474162541868495935751340 : ℤ)⟩ := by
  rw [show (JIC).value = dInv (JC).value from rfl, ev_C]
  exact op_IC

theorem p0_IC : (JIC).part 0 = ⟨(205 : ℤ), (-1135536032641037844269706298458384243338372187355507939235139 : ℤ), (-1028208831207113637940525315110250902283392473429318390718267 : ℤ)⟩ := by
  rw [show (JIC).part 0 = dNeg (dMul (dMul (dInv (JC).value) (dInv (JC).value)) ((JC).part 0)) from rfl, ev_C, op_IC, p0_C]
  rfl

theorem p1_IC : (JIC).part 1 = ⟨(207 : ℤ), (867365165876596508225041121486622966779846400851498727016989 : ℤ), (956449808424679442133887257359502219409604316967104681827224 : ℤ)⟩ := by
  rw [show (JIC).part 1 = dNeg (dMul (dMul (dInv (JC).value) (dInv (JC).value)) ((JC).part 1)) from rfl, ev_C, op_IC, p1_C]
  rfl

theorem p2_IC : (JIC).part 2 = ⟨(205 : ℤ), (-1164589048546518011611349865655212593998846318514035970674000 : ℤ), (-1063826869657501557436233136565426961286947096024792310479520 : ℤ)⟩ := by
  rw [show (JIC).part 2 = dNeg (dMul (dMul (dInv (JC).value) (dInv (JC).value)) ((JC).part 2)) from rfl, ev_C, op_IC, p2_C]
  rfl

def JWA : DCJet := DCJetKit.mul JNA JInvD4A
theorem JWA_mem : JetMem JWA fWA D :=
  DCJetKit.mul_mem (JNA_mem) (JInvD4A_mem)

theorem op_WA : dMul ⟨(197 : ℤ), (914294223832883731526888470543487633156320138947416727100993 : ℤ), (933710527875502855212885292757040016724189579240055687286716 : ℤ)⟩ ⟨(205 : ℤ), (1416031424258160552026942061213876800307553066984693798063993 : ℤ), (1590607037371427492752460293552287084972755165387525452792960 : ℤ)⟩ = ⟨(202 : ℤ), (805674715705732506325785719279213913857658278551759208058092 : ℤ), (924221404684847268124964401432519966721484197636067322064598 : ℤ)⟩ := by
  rfl

theorem ev_WA : (JWA).value = ⟨(202 : ℤ), (805674715705732506325785719279213913857658278551759208058092 : ℤ), (924221404684847268124964401432519966721484197636067322064598 : ℤ)⟩ := by
  rw [show (JWA).value = dMul (JNA).value (JInvD4A).value from rfl, ev_NA, ev_InvD4A]
  exact op_WA

theorem p0_WA : (JWA).part 0 = ⟨(203 : ℤ), (-1556670055676301703995700835136366986237331780167207231158140 : ℤ), (-1158344433345021088097262104028604858955151539891752715240651 : ℤ)⟩ := by
  rw [show (JWA).part 0 = dAdd (dMul (JNA).value ((JInvD4A).part 0)) (dMul (JInvD4A).value ((JNA).part 0)) from rfl, ev_NA, ev_InvD4A, p0_NA, p0_InvD4A]
  rfl

theorem p1_WA : (JWA).part 1 = ⟨(204 : ℤ), (538623539130922026788052992366656034665505722574523141725461 : ℤ), (1297773074807889056019177803299373196819754384659825126675812 : ℤ)⟩ := by
  rw [show (JWA).part 1 = dAdd (dMul (JNA).value ((JInvD4A).part 1)) (dMul (JInvD4A).value ((JNA).part 1)) from rfl, ev_NA, ev_InvD4A, p1_NA, p1_InvD4A]
  rfl

theorem p2_WA : (JWA).part 2 = ⟨(203 : ℤ), (-1455483674416194208073521427298835973958118230509284478289335 : ℤ), (-1057523595996723443116618967286065295620523677184277051779293 : ℤ)⟩ := by
  rw [show (JWA).part 2 = dAdd (dMul (JNA).value ((JInvD4A).part 2)) (dMul (JInvD4A).value ((JNA).part 2)) from rfl, ev_NA, ev_InvD4A, p2_NA, p2_InvD4A]
  rfl

def JWB : DCJet := DCJetKit.mul JNB JInvD4B
theorem JWB_mem : JetMem JWB fWB D :=
  DCJetKit.mul_mem (JNB_mem) (JInvD4B_mem)

theorem op_WB : dMul ⟨(197 : ℤ), (924255476712425522693540247044719616497443334201105564474060 : ℤ), (946565016031650525975666202218436093485229164904776718535215 : ℤ)⟩ ⟨(204 : ℤ), (716992299129643258382373053186858070659404380172097447504591 : ℤ), (812521210549628783580584286488869997300344157056145111545713 : ℤ)⟩ = ⟨(202 : ℤ), (824778604998167072925775170681264149506537821507188542539185 : ℤ), (957229378491220675534825900697903711677715805676017971467802 : ℤ)⟩ := by
  rfl

theorem ev_WB : (JWB).value = ⟨(202 : ℤ), (824778604998167072925775170681264149506537821507188542539185 : ℤ), (957229378491220675534825900697903711677715805676017971467802 : ℤ)⟩ := by
  rw [show (JWB).value = dMul (JNB).value (JInvD4B).value from rfl, ev_NB, ev_InvD4B]
  exact op_WB

theorem p0_WB : (JWB).part 0 = ⟨(202 : ℤ), (-846417751231315427561050833040382614812261566837695190961709 : ℤ), (-613577013546099877191593561888397021153897134043596666877338 : ℤ)⟩ := by
  rw [show (JWB).part 0 = dAdd (dMul (JNB).value ((JInvD4B).part 0)) (dMul (JInvD4B).value ((JNB).part 0)) from rfl, ev_NB, ev_InvD4B, p0_NB, p0_InvD4B]
  rfl

theorem p1_WB : (JWB).part 1 = ⟨(203 : ℤ), (-1561303495215207430273245156158348185857852004278507789953372 : ℤ), (-1108269472671352090018793549326257731935166903680928903757472 : ℤ)⟩ := by
  rw [show (JWB).part 1 = dAdd (dMul (JNB).value ((JInvD4B).part 1)) (dMul (JInvD4B).value ((JNB).part 1)) from rfl, ev_NB, ev_InvD4B, p1_NB, p1_InvD4B]
  rfl

theorem p2_WB : (JWB).part 2 = ⟨(204 : ℤ), (697873615116048846283518350555703916638632815976033803268648 : ℤ), (1501155547533102681524325231029524698385397611063705142400992 : ℤ)⟩ := by
  rw [show (JWB).part 2 = dAdd (dMul (JNB).value ((JInvD4B).part 2)) (dMul (JInvD4B).value ((JNB).part 2)) from rfl, ev_NB, ev_InvD4B, p2_NB, p2_InvD4B]
  rfl

def JWC : DCJet := DCJetKit.mul JNC JInvD4C
theorem JWC_mem : JetMem JWC fWC D :=
  DCJetKit.mul_mem (JNC_mem) (JInvD4C_mem)

theorem op_WC : dMul ⟨(197 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883412965057676704257544199132921689698176452925934 : ℤ)⟩ ⟨(204 : ℤ), (879554236223886780586152194374509245039384312461527462552798 : ℤ), (982171187972126533137383487664930032701012744908221515451680 : ℤ)⟩ = ⟨(202 : ℤ), (1108238337642097343538551764911881648749624233701524602816524 : ℤ), (1237535696845183924464798313125615092832121940193097077440295 : ℤ)⟩ := by
  rfl

theorem ev_WC : (JWC).value = ⟨(202 : ℤ), (1108238337642097343538551764911881648749624233701524602816524 : ℤ), (1237535696845183924464798313125615092832121940193097077440295 : ℤ)⟩ := by
  rw [show (JWC).value = dMul (JNC).value (JInvD4C).value from rfl, ev_NC, ev_InvD4C]
  exact op_WC

theorem p0_WC : (JWC).part 0 = ⟨(202 : ℤ), (773634913768603891499555854060781084991085492031547787120416 : ℤ), (1021978856246537948033566045239425486733624911678451239522390 : ℤ)⟩ := by
  rw [show (JWC).part 0 = dAdd (dMul (JNC).value ((JInvD4C).part 0)) (dMul (JInvD4C).value ((JNC).part 0)) from rfl, ev_NC, ev_InvD4C, p0_NC, p0_InvD4C]
  rfl

theorem p1_WC : (JWC).part 1 = ⟨(202 : ℤ), (-1395500514490516788033558303880391765835283319128091303363285 : ℤ), (-1095858778128794954828421818390238787365430375702037124441706 : ℤ)⟩ := by
  rw [show (JWC).part 1 = dAdd (dMul (JNC).value ((JInvD4C).part 1)) (dMul (JInvD4C).value ((JNC).part 1)) from rfl, ev_NC, ev_InvD4C, p1_NC, p1_InvD4C]
  rfl

theorem p2_WC : (JWC).part 2 = ⟨(202 : ℤ), (-1414712512534741655072536504000935216414781777473804817351436 : ℤ), (-1107798180265061623308749070026886694104720548553047041311836 : ℤ)⟩ := by
  rw [show (JWC).part 2 = dAdd (dMul (JNC).value ((JInvD4C).part 2)) (dMul (JInvD4C).value ((JNC).part 2)) from rfl, ev_NC, ev_InvD4C, p2_NC, p2_InvD4C]
  rfl

theorem mv_MtA : dMatan9 ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ = ⟨(200 : ℤ), (1604730203322641142879714480343472727742261688946434233401245 : ℤ), (1605641925430842680491493087066587169276228384457797001590987 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtAa : dAdd ONE ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ = ⟨(199 : ℤ), (805418019098297214785519199664486612278277993600391801035439 : ℤ), (806785596391865560428959066029541523554187106103608614840423 : ℤ)⟩ := by rfl
theorem mdMtAb : dInv ⟨(199 : ℤ), (805418019098297214785519199664486612278277993600391801035439 : ℤ), (806785596391865560428959066029541523554187106103608614840423 : ℤ)⟩ = ⟨(200 : ℤ), (1600332163610341941035725096468785772617993414261333974528384 : ℤ), (1603049482911902664415498754579960027486011845607998525046501 : ℤ)⟩ := by rfl
theorem mdMtAc : dSub ⟨(200 : ℤ), (1600332163610341941035725096468785772617993414261333974528384 : ℤ), (1603049482911902664415498754579960027486011845607998525046501 : ℤ)⟩ ⟨(200 : ℤ), (1604730203322641142879714480343472727742261688946434233401245 : ℤ), (1605641925430842680491493087066587169276228384457797001590987 : ℤ)⟩ = ⟨(200 : ℤ), (-5309761820500739455767990597801396658234970196463027062603 : ℤ), (-1680720410738478464215725763512700256249843338435708354744 : ℤ)⟩ := by rfl
theorem mdMtAd : dMul (dInt 2) ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ = ⟨(206 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ := by rfl
theorem mdMtAe : dInv ⟨(206 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ = ⟨(192 : ℤ), (760341303127316804556136476566116310737758927496014459192114 : ℤ), (1293859578508832057671985523666955396187740446877566373916721 : ℤ)⟩ := by rfl
theorem mdMtAf : dMul ⟨(200 : ℤ), (-5309761820500739455767990597801396658234970196463027062603 : ℤ), (-1680720410738478464215725763512700256249843338435708354744 : ℤ)⟩ ⟨(192 : ℤ), (760341303127316804556136476566116310737758927496014459192114 : ℤ), (1293859578508832057671985523666955396187740446877566373916721 : ℤ)⟩ = ⟨(200 : ℤ), (-1094467873975307787535636707984867554092975128281977919194098 : ℤ), (-203584584281849562409780960354757470422368006659739566093559 : ℤ)⟩ := by rfl

theorem md_MtA : dMatanD ⟨(207 : ℤ), (498943224013331715721767294439759620397183157502818146496499 : ℤ), (849043011166828200442373083893816907029915958326322480572084 : ℤ)⟩ ⟨(200 : ℤ), (1604730203322641142879714480343472727742261688946434233401245 : ℤ), (1605641925430842680491493087066587169276228384457797001590987 : ℤ)⟩ = ⟨(200 : ℤ), (-1094467873975307787535636707984867554092975128281977919194098 : ℤ), (-203584584281849562409780960354757470422368006659739566093559 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtAa, mdMtAb, mdMtAc, mdMtAd, mdMtAe]
  exact mdMtAf

theorem BMtA_gates : (dLoBig JTA.value = true ∧
    dLoBig (dAdd ONE JTA.value) = true ∧
    dLoBig (dMul (dInt 2) JTA.value) = true) := by
  rw [ev_TA]
  decide
theorem BMtA_hbig : dLoBig JTA.value = true := BMtA_gates.1
theorem BMtA_hden1 : dLoBig (dAdd ONE JTA.value) = true :=
  BMtA_gates.2.1
theorem BMtA_hden2 : dLoBig (dMul (dInt 2) JTA.value) = true :=
  BMtA_gates.2.2

def JMtA : DCJet := DCJetKit.matan9 JTA
theorem JMtA_mem : JetMem JMtA fMtA D :=
  DCJetKit.matan9_mem (JTA_mem) BMtA_hbig BMtA_hden1 BMtA_hden2

theorem ev_MtA : (JMtA).value = ⟨(200 : ℤ), (1604730203322641142879714480343472727742261688946434233401245 : ℤ), (1605641925430842680491493087066587169276228384457797001590987 : ℤ)⟩ := by
  rw [show (JMtA).value = dMatan9 (JTA).value from rfl, ev_TA]
  exact mv_MtA

theorem p0_MtA : (JMtA).part 0 = ⟨(205 : ℤ), (118143243468054720953788054497904413457421129854711057428489 : ℤ), (1052147630534498162691242480482682387386532268173963167408425 : ℤ)⟩ := by
  rw [show (JMtA).part 0 = DCJetKit.matanSlot (JTA).value (dMatan9 (JTA).value) ((JTA).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_TA, mv_MtA, md_MtA, p0_TA]
  rfl

theorem p1_MtA : (JMtA).part 1 = ⟨(205 : ℤ), (75632019216568782477439679872814395969566304123387543064305 : ℤ), (855478922529147105579129515308551214402877334088909256834575 : ℤ)⟩ := by
  rw [show (JMtA).part 1 = DCJetKit.matanSlot (JTA).value (dMatan9 (JTA).value) ((JTA).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_TA, mv_MtA, md_MtA, p1_TA]
  rfl

theorem p2_MtA : (JMtA).part 2 = ⟨(206 : ℤ), (107162607469735624685922943274287256319162880952712421026529 : ℤ), (1351955054932950395261566686002429213390691169053029267313869 : ℤ)⟩ := by
  rw [show (JMtA).part 2 = DCJetKit.matanSlot (JTA).value (dMatan9 (JTA).value) ((JTA).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_TA, mv_MtA, md_MtA, p2_TA]
  rfl

theorem mv_MtB : dMatan9 ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ = ⟨(200 : ℤ), (1603917347830861521883745325722975129271067219867434998704289 : ℤ), (1605269074625382975530986098186848528785278927018903761838548 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtBa : dAdd ONE ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ = ⟨(199 : ℤ), (805980973021795449931594394835966974384935909997561779438233 : ℤ), (808008547864072044698698067733305538178103751793977809346461 : ℤ)⟩ := by rfl
theorem mdMtBb : dInv ⟨(199 : ℤ), (805980973021795449931594394835966974384935909997561779438233 : ℤ), (808008547864072044698698067733305538178103751793977809346461 : ℤ)⟩ = ⟨(200 : ℤ), (1597910000403430056210618676818228891001914819131083171798235 : ℤ), (1601929800157378546546284818027891187402802302574110895822726 : ℤ)⟩ := by rfl
theorem mdMtBc : dSub ⟨(200 : ℤ), (1597910000403430056210618676818228891001914819131083171798235 : ℤ), (1601929800157378546546284818027891187402802302574110895822726 : ℤ)⟩ ⟨(200 : ℤ), (1603917347830861521883745325722975129271067219867434998704289 : ℤ), (1605269074625382975530986098186848528785278927018903761838548 : ℤ)⟩ = ⟨(200 : ℤ), (-7359074221952919320367421368619637783364107887820590040313 : ℤ), (-1987547673482975337460507695083941868264917293324102881563 : ℤ)⟩ := by rfl
theorem mdMtBd : dMul (dInt 2) ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ = ⟨(206 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ := by rfl
theorem mdMtBe : dInv ⟨(206 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ = ⟨(192 : ℤ), (555504813501024663273109531201911106067648617544730804052732 : ℤ), (1003892394671768756663524431516751591156736042955367770075333 : ℤ)⟩ := by rfl
theorem mdMtBf : dMul ⟨(200 : ℤ), (-7359074221952919320367421368619637783364107887820590040313 : ℤ), (-1987547673482975337460507695083941868264917293324102881563 : ℤ)⟩ ⟨(192 : ℤ), (555504813501024663273109531201911106067648617544730804052732 : ℤ), (1003892394671768756663524431516751591156736042955367770075333 : ℤ)⟩ = ⟨(200 : ℤ), (-1176931481227379359647262356859662063678847749129006106297422 : ℤ), (-175892051176790685656138406343168944344307714795315543331592 : ℤ)⟩ := by rfl

theorem md_MtB : dMatanD ⟨(207 : ℤ), (643059428428879913117017258338732319701609755178332617611655 : ℤ), (1162118588051688173495557520057404650752577255060836274117805 : ℤ)⟩ ⟨(200 : ℤ), (1603917347830861521883745325722975129271067219867434998704289 : ℤ), (1605269074625382975530986098186848528785278927018903761838548 : ℤ)⟩ = ⟨(200 : ℤ), (-1176931481227379359647262356859662063678847749129006106297422 : ℤ), (-175892051176790685656138406343168944344307714795315543331592 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtBa, mdMtBb, mdMtBc, mdMtBd, mdMtBe]
  exact mdMtBf

theorem BMtB_gates : (dLoBig JTB.value = true ∧
    dLoBig (dAdd ONE JTB.value) = true ∧
    dLoBig (dMul (dInt 2) JTB.value) = true) := by
  rw [ev_TB]
  decide
theorem BMtB_hbig : dLoBig JTB.value = true := BMtB_gates.1
theorem BMtB_hden1 : dLoBig (dAdd ONE JTB.value) = true :=
  BMtB_gates.2.1
theorem BMtB_hden2 : dLoBig (dMul (dInt 2) JTB.value) = true :=
  BMtB_gates.2.2

def JMtB : DCJet := DCJetKit.matan9 JTB
theorem JMtB_mem : JetMem JMtB fMtB D :=
  DCJetKit.matan9_mem (JTB_mem) BMtB_hbig BMtB_hden1 BMtB_hden2

theorem ev_MtB : (JMtB).value = ⟨(200 : ℤ), (1603917347830861521883745325722975129271067219867434998704289 : ℤ), (1605269074625382975530986098186848528785278927018903761838548 : ℤ)⟩ := by
  rw [show (JMtB).value = dMatan9 (JTB).value from rfl, ev_TB]
  exact mv_MtB

theorem p0_MtB : (JMtB).part 0 = ⟨(205 : ℤ), (101724512241504632661005967807508312372665740817917739245504 : ℤ), (1255176394948708017114792498887346774761298879428514314930844 : ℤ)⟩ := by
  rw [show (JMtB).part 0 = DCJetKit.matanSlot (JTB).value (dMatan9 (JTB).value) ((JTB).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_TB, mv_MtB, md_MtB, p0_TB]
  rfl

theorem p1_MtB : (JMtB).part 1 = ⟨(205 : ℤ), (84370349619042864591847904199137855395624761816782138976010 : ℤ), (1293743321602854048543347419296311584483677162380678327266645 : ℤ)⟩ := by
  rw [show (JMtB).part 1 = DCJetKit.matanSlot (JTB).value (dMatan9 (JTB).value) ((JTB).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_TB, mv_MtB, md_MtB, p1_TB]
  rfl

theorem p2_MtB : (JMtB).part 2 = ⟨(205 : ℤ), (87376586003855784481445385012448114044556181570445163273076 : ℤ), (1325520730757981536686272868376569834828798606860434610359598 : ℤ)⟩ := by
  rw [show (JMtB).part 2 = DCJetKit.matanSlot (JTB).value (dMatan9 (JTB).value) ((JTB).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_TB, mv_MtB, md_MtB, p2_TB]
  rfl

theorem mv_MtC : dMatan9 ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ = ⟨(200 : ℤ), (1604811718214045392090808563178259044727923678252804556964385 : ℤ), (1605696623234591478782933069388591805028820262585086826493200 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtCa : dAdd ONE ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ = ⟨(199 : ℤ), (805335598279322536722937666122005536561828825389574225748384 : ℤ), (806662950556648483035221531043291777073167750490434422267430 : ℤ)⟩ := by rfl
theorem mdMtCb : dInv ⟨(199 : ℤ), (805335598279322536722937666122005536561828825389574225748384 : ℤ), (806662950556648483035221531043291777073167750490434422267430 : ℤ)⟩ = ⟨(200 : ℤ), (1600575479700036281658358519907271664499823269119536984159183 : ℤ), (1603213544517425666640877700820657924044588547165762377144760 : ℤ)⟩ := by rfl
theorem mdMtCc : dSub ⟨(200 : ℤ), (1600575479700036281658358519907271664499823269119536984159183 : ℤ), (1603213544517425666640877700820657924044588547165762377144760 : ℤ)⟩ ⟨(200 : ℤ), (1604811718214045392090808563178259044727923678252804556964385 : ℤ), (1605696623234591478782933069388591805028820262585086826493200 : ℤ)⟩ = ⟨(200 : ℤ), (-5121143534555197124574549481320140528996993465549842334017 : ℤ), (-1598173696619725449930862357601120683335131087042179819625 : ℤ)⟩ := by rfl
theorem mdMtCd : dMul (dInt 2) ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ = ⟨(206 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ := by rfl
theorem mdMtCe : dInv ⟨(206 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ = ⟨(192 : ℤ), (789538167208333228785702084488168467524459171144406853720777 : ℤ), (1350991437880757882640743240069768409093174884321145411776505 : ℤ)⟩ := by rfl
theorem mdMtCf : dMul ⟨(200 : ℤ), (-5121143534555197124574549481320140528996993465549842334017 : ℤ), (-1598173696619725449930862357601120683335131087042179819625 : ℤ)⟩ ⟨(192 : ℤ), (789538167208333228785702084488168467524459171144406853720777 : ℤ), (1350991437880757882640743240069768409093174884321145411776505 : ℤ)⟩ = ⟨(200 : ℤ), (-1102199925857386624961419590645580039383593126627669113817627 : ℤ), (-201019385140166839237476750488306476211898645168658745075110 : ℤ)⟩ := by rfl

theorem md_MtC : dMatanD ⟨(207 : ℤ), (477843494355814131700894707564604236986196095533518873010380 : ℤ), (817645677351256387645564127413881807888960921353729181885871 : ℤ)⟩ ⟨(200 : ℤ), (1604811718214045392090808563178259044727923678252804556964385 : ℤ), (1605696623234591478782933069388591805028820262585086826493200 : ℤ)⟩ = ⟨(200 : ℤ), (-1102199925857386624961419590645580039383593126627669113817627 : ℤ), (-201019385140166839237476750488306476211898645168658745075110 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtCa, mdMtCb, mdMtCc, mdMtCd, mdMtCe]
  exact mdMtCf

theorem BMtC_gates : (dLoBig JTC.value = true ∧
    dLoBig (dAdd ONE JTC.value) = true ∧
    dLoBig (dMul (dInt 2) JTC.value) = true) := by
  rw [ev_TC]
  decide
theorem BMtC_hbig : dLoBig JTC.value = true := BMtC_gates.1
theorem BMtC_hden1 : dLoBig (dAdd ONE JTC.value) = true :=
  BMtC_gates.2.1
theorem BMtC_hden2 : dLoBig (dMul (dInt 2) JTC.value) = true :=
  BMtC_gates.2.2

def JMtC : DCJet := DCJetKit.matan9 JTC
theorem JMtC_mem : JetMem JMtC fMtC D :=
  DCJetKit.matan9_mem (JTC_mem) BMtC_hbig BMtC_hden1 BMtC_hden2

theorem ev_MtC : (JMtC).value = ⟨(200 : ℤ), (1604811718214045392090808563178259044727923678252804556964385 : ℤ), (1605696623234591478782933069388591805028820262585086826493200 : ℤ)⟩ := by
  rw [show (JMtC).value = dMatan9 (JTC).value from rfl, ev_TC]
  exact mv_MtC

theorem p0_MtC : (JMtC).part 0 = ⟨(205 : ℤ), (111494077072790187618634319107543639222756899622723923352171 : ℤ), (1019861283029517696672280239130973223502803810107580462890028 : ℤ)⟩ := by
  rw [show (JMtC).part 0 = DCJetKit.matanSlot (JTC).value (dMatan9 (JTC).value) ((JTC).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_TC, mv_MtC, md_MtC, p0_TC]
  rfl

theorem p1_MtC : (JMtC).part 1 = ⟨(206 : ℤ), (96420464654822920825370015794701478259583124677582149884631 : ℤ), (1268798162752295086897406909051876715731302744199512537858944 : ℤ)⟩ := by
  rw [show (JMtC).part 1 = DCJetKit.matanSlot (JTC).value (dMatan9 (JTC).value) ((JTC).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_TC, mv_MtC, md_MtC, p1_TC]
  rfl

theorem p2_MtC : (JMtC).part 2 = ⟨(205 : ℤ), (73839166044564905337962472253563789494317597095423136044340 : ℤ), (850166215789590763172134567561607550932481585844217465883217 : ℤ)⟩ := by
  rw [show (JMtC).part 2 = DCJetKit.matanSlot (JTC).value (dMatan9 (JTC).value) ((JTC).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_TC, mv_MtC, md_MtC, p2_TC]
  rfl

/-- literal square root `dSqrt ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgA : dSqrt ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(201 : ℤ), (1072833932447179157642143864418775657326243492171307630018619 : ℤ), (1549250192290764551073539628989499030529767152210118917629475 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1072833932447179157642143864418775657326243492171307630018619 : ℤ)) (rhi := (1549250192290764551073539628989499030529767152210118917629474 : ℤ))
    (nlo := 1150972646610078572203307300977677319489766354432330175865358253363532819398295690902288976296882320068288058973929603072) (nhi := 2400176158312970937239494176824177313477195860239399157456586564193356365737348458017024165007798719866347574480552853504) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgA : dSqrt (dInv ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩) = ⟨(198 : ℤ), (833386980016675643383026897650046333416904155876789634879395 : ℤ), (1203471385453239909673695829843033994815747493978165495212324 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩)) (K := (198 : ℤ))
    (rlo := (833386980016675643383026897650046333416904155876789634879395 : ℤ)) (rhi := (1203471385453239909673695829843033994815747493978165495212323 : ℤ))
    (nlo := 694533858461314928157353616064920310088702698333671528964488124358655281919532372784620322398840752653569696808426274816) (nhi := 1448343375604740748869981652540860863363319408112649922175914339392542197163605534771101340359210731836673326319044395008) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem u9_MgA : dMatanU9 (dInv ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩) = ⟨(200 : ℤ), (592374633042392430493143409568818299067866812068831372383478 : ℤ), (977094773616835763328800914360659923696078800542909079794582 : ℤ)⟩ := by
  unfold dMatanU9
  rw [sqi_MgA]
  rfl

theorem mt_MgA : DCJetKit.dMatanTight ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(200 : ℤ), (592374633042392430493143409568818299067866812068831372383478 : ℤ), (977094773616835763328800914360659923696078800542909079794582 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_neg (by decide)]
  exact u9_MgA

theorem mMgAa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgAb : dInv ⟨(201 : ℤ), (1072833932447179157642143864418775657326243492171307630018619 : ℤ), (1549250192290764551073539628989499030529767152210118917629475 : ℤ)⟩ = ⟨(198 : ℤ), (833386980016675643383026897650046333416904155876789634879395 : ℤ), (1203471385453239909673695829843033994815747493978165495212324 : ℤ)⟩ := by rfl
theorem mMgAc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(198 : ℤ), (833386980016675643383026897650046333416904155876789634879395 : ℤ), (1203471385453239909673695829843033994815747493978165495212324 : ℤ)⟩ = ⟨(197 : ℤ), (654540603504322328626144942914226695840537638889964245558770 : ℤ), (945204215836456585879665359058385438677859758949621336565523 : ℤ)⟩ := by rfl
theorem mMgAd : dInv ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(196 : ℤ), (432209481219661058397609950649868564216644539311131482446566 : ℤ), (901306295397727968084137913420104539507309955175533447655883 : ℤ)⟩ := by rfl
theorem mMgAe : dMul ⟨(200 : ℤ), (592374633042392430493143409568818299067866812068831372383478 : ℤ), (977094773616835763328800914360659923696078800542909079794582 : ℤ)⟩ ⟨(196 : ℤ), (432209481219661058397609950649868564216644539311131482446566 : ℤ), (901306295397727968084137913420104539507309955175533447655883 : ℤ)⟩ = ⟨(197 : ℤ), (318655636724318123947089217074837759478654237419365069094304 : ℤ), (1096074206230113536427849970044221851735017000199571594580397 : ℤ)⟩ := by rfl
theorem mMgAf : dSub ⟨(197 : ℤ), (654540603504322328626144942914226695840537638889964245558770 : ℤ), (945204215836456585879665359058385438677859758949621336565523 : ℤ)⟩ ⟨(197 : ℤ), (318655636724318123947089217074837759478654237419365069094304 : ℤ), (1096074206230113536427849970044221851735017000199571594580397 : ℤ)⟩ = ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ := by rfl

theorem mv_MgA : dMatanMir ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ ⟨(200 : ℤ), (592374633042392430493143409568818299067866812068831372383478 : ℤ), (977094773616835763328800914360659923696078800542909079794582 : ℤ)⟩ = ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgA, mMgAa, mMgAb, mMgAc, mMgAd, mMgAe]
  exact mMgAf

theorem mdMgAa : dAdd ONE ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(199 : ℤ), (893000526682680034855599214848602402348696590612117102365259 : ℤ), (990173183413741143822412216300808482341714061892467325212158 : ℤ)⟩ := by rfl
theorem mdMgAb : dInv ⟨(199 : ℤ), (893000526682680034855599214848602402348696590612117102365259 : ℤ), (990173183413741143822412216300808482341714061892467325212158 : ℤ)⟩ = ⟨(200 : ℤ), (1303938503557676422036489370459096875928687817969081162725448 : ℤ), (1445827746417717741084868717842122581285366104566829719243638 : ℤ)⟩ := by rfl
theorem mdMgAc : dSub ⟨(200 : ℤ), (1303938503557676422036489370459096875928687817969081162725448 : ℤ), (1445827746417717741084868717842122581285366104566829719243638 : ℤ)⟩ ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ = ⟨(198 : ℤ), (-927112532334857818356029941352321139416239088568242244261076 : ℤ), (1244524142056011850874627233720520957110300248760922127854164 : ℤ)⟩ := by rfl
theorem mdMgAd : dMul (dInt 2) ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(201 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ := by rfl
theorem mdMgAe : dInv ⟨(201 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ = ⟨(197 : ℤ), (432209481219661058397609950649868564216644539311131482446566 : ℤ), (901306295397727968084137913420104539507309955175533447655883 : ℤ)⟩ := by rfl
theorem mdMgAf : dMul ⟨(198 : ℤ), (-927112532334857818356029941352321139416239088568242244261076 : ℤ), (1244524142056011850874627233720520957110300248760922127854164 : ℤ)⟩ ⟨(197 : ℤ), (432209481219661058397609950649868564216644539311131482446566 : ℤ), (901306295397727968084137913420104539507309955175533447655883 : ℤ)⟩ = ⟨(196 : ℤ), (-1040005698938896118409953032035785254514522613968247536305912 : ℤ), (1396068066241831729840907654126585332490002635885877378980403 : ℤ)⟩ := by rfl

theorem md_MgA : dMatanD ⟨(202 : ℤ), (716252036425479176676945349424168808700760749765765477716572 : ℤ), (1493633290273968048411449361041817448644900520008567260491754 : ℤ)⟩ ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ = ⟨(196 : ℤ), (-1040005698938896118409953032035785254514522613968247536305912 : ℤ), (1396068066241831729840907654126585332490002635885877378980403 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgAa, mdMgAb, mdMgAc, mdMgAd, mdMgAe]
  exact mdMgAf

theorem BMgA_gates : (dLoBig JGA.value = true ∧
    dLoGt (dInv JGA.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGA.value)) ONE) = true ∧
    dLoBig (dInv JGA.value) = true ∧
    dLoBig (dAdd ONE JGA.value) = true ∧
    dLoBig (dMul (dInt 2) JGA.value) = true) := by
  rw [ev_GA, sqi_MgA]
  decide
theorem BMgA_hbig : dLoBig JGA.value = true := BMgA_gates.1
theorem BMgA_hR1 : dLoGt (dInv JGA.value) ONE = true :=
  BMgA_gates.2.1
theorem BMgA_hRden : dLoBig (dAdd (dSqrt (dInv JGA.value)) ONE) = true :=
  BMgA_gates.2.2.1
theorem BMgA_hRbig : dLoBig (dInv JGA.value) = true :=
  BMgA_gates.2.2.2.1
theorem BMgA_hden1 : dLoBig (dAdd ONE JGA.value) = true :=
  BMgA_gates.2.2.2.2.1
theorem BMgA_hden2 : dLoBig (dMul (dInt 2) JGA.value) = true :=
  BMgA_gates.2.2.2.2.2

def JMgA : DCJet := DCJetKit.matanMir JGA (DCJetKit.dMatanTight JGA.value)
theorem JMgA_mem : JetMem JMgA fMgA D :=
  DCJetKit.matanMir_mem (JGA_mem) (DCJetKit.dMatanTight JGA.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGA_mem.2.1 x hx) BMgA_hbig BMgA_hR1 BMgA_hRden BMgA_hRbig)
    BMgA_hbig BMgA_hden1 BMgA_hden2

theorem ev_MgA : (JMgA).value = ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ := by
  rw [show (JMgA).value = dMatanMir (JGA).value (DCJetKit.dMatanTight (JGA).value) from rfl, ev_GA, mt_MgA]
  exact mv_MgA

theorem p0_MgA : (JMgA).part 0 = ⟨(195 : ℤ), (-1288843314659950710146973720382721710259750763792075676049283 : ℤ), (960128252123099691505147720896993616218751418756598211288237 : ℤ)⟩ := by
  rw [show (JMgA).part 0 = DCJetKit.matanSlot (JGA).value (dMatanMir (JGA).value (DCJetKit.dMatanTight (JGA).value)) ((JGA).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_GA, mt_MgA, mv_MgA, md_MgA, p0_GA]
  rfl

theorem p1_MgA : (JMgA).part 1 = ⟨(196 : ℤ), (-1510858587091350570012572313113355384600145705302397374936780 : ℤ), (1125519291545478861323142775259047447980846021194060107381773 : ℤ)⟩ := by
  rw [show (JMgA).part 1 = DCJetKit.matanSlot (JGA).value (dMatanMir (JGA).value (DCJetKit.dMatanTight (JGA).value)) ((JGA).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_GA, mt_MgA, mv_MgA, md_MgA, p1_GA]
  rfl

theorem p2_MgA : (JMgA).part 2 = ⟨(195 : ℤ), (-1067511819763287138941896913230211327602757635475173598294343 : ℤ), (795246595122772817506416692950327658918227605221733243414069 : ℤ)⟩ := by
  rw [show (JMgA).part 2 = DCJetKit.matanSlot (JGA).value (dMatanMir (JGA).value (DCJetKit.dMatanTight (JGA).value)) ((JGA).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_GA, mt_MgA, mv_MgA, md_MgA, p2_GA]
  rfl

/-- literal square root `dSqrt ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgB : dSqrt ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(201 : ℤ), (1098272611699618192163936757855484828171097419279106072332554 : ℤ), (1604580667767136007154891256420766298882593395698731555007699 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1098272611699618192163936757855484828171097419279106072332554 : ℤ)) (rhi := (1604580667767136007154891256420766298882593395698731555007698 : ℤ))
    (nlo := 1206202729609500318711438740984371306105982480927206680395086055845870836417380830253882432204706469491035475185231724544) (nhi := 2574679119372028101669122022553751809987976973245657315148029677523605303275559519021705717855684442256619589035634982912) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgB : dSqrt (dInv ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩) = ⟨(198 : ℤ), (804649442050256694694499026299883137673814904785947929609872 : ℤ), (1175596045361988832166854035743923466802188868180315812666666 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩)) (K := (198 : ℤ))
    (rlo := (804649442050256694694499026299883137673814904785947929609872 : ℤ)) (rhi := (1175596045361988832166854035743923466802188868180315812666665 : ℤ))
    (nlo := 647460724591789406687911739325104669367319937997743607114718072533570844197891263496891629342792703117585705587231948800) (nhi := 1382026061870747303990080683639212939765382544485875969203464097887774510434124587739254679522025929820103335596332679168) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem u9_MgB : dMatanU9 (dInv ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩) = ⟨(200 : ℤ), (597599308098350883255532322094667566717507237919138815064871 : ℤ), (1007516983042222219763525434586952427885032074464181776518883 : ℤ)⟩ := by
  unfold dMatanU9
  rw [sqi_MgB]
  rfl

theorem mt_MgB : DCJetKit.dMatanTight ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(200 : ℤ), (597599308098350883255532322094667566717507237919138815064871 : ℤ), (1007516983042222219763525434586952427885032074464181776518883 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_neg (by decide)]
  exact u9_MgB

theorem mMgBa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgBb : dInv ⟨(201 : ℤ), (1098272611699618192163936757855484828171097419279106072332554 : ℤ), (1604580667767136007154891256420766298882593395698731555007699 : ℤ)⟩ = ⟨(198 : ℤ), (804649442050256694694499026299883137673814904785947929609872 : ℤ), (1175596045361988832166854035743923466802188868180315812666666 : ℤ)⟩ := by rfl
theorem mMgBc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(198 : ℤ), (804649442050256694694499026299883137673814904785947929609872 : ℤ), (1175596045361988832166854035743923466802188868180315812666666 : ℤ)⟩ = ⟨(197 : ℤ), (631970193964936606052300458929449799161169708541336272223783 : ℤ), (923310974924706428768605433444880221841567932147320701427925 : ℤ)⟩ := by rfl
theorem mMgBd : dInv ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(196 : ℤ), (402915798094975050026934694955562331709873555089728989301925 : ℤ), (860036929742392795437379837437597272213734286725855694251293 : ℤ)⟩ := by rfl
theorem mMgBe : dMul ⟨(200 : ℤ), (597599308098350883255532322094667566717507237919138815064871 : ℤ), (1007516983042222219763525434586952427885032074464181776518883 : ℤ)⟩ ⟨(196 : ℤ), (402915798094975050026934694955562331709873555089728989301925 : ℤ), (860036929742392795437379837437597272213734286725855694251293 : ℤ)⟩ = ⟨(197 : ℤ), (299678264540042285090150991524325840542452616674266514494475 : ℤ), (1078450803818665568033079366330916102907921538371555185523110 : ℤ)⟩ := by rfl
theorem mMgBf : dSub ⟨(197 : ℤ), (631970193964936606052300458929449799161169708541336272223783 : ℤ), (923310974924706428768605433444880221841567932147320701427925 : ℤ)⟩ ⟨(197 : ℤ), (299678264540042285090150991524325840542452616674266514494475 : ℤ), (1078450803818665568033079366330916102907921538371555185523110 : ℤ)⟩ = ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ := by rfl

theorem mv_MgB : dMatanMir ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ ⟨(200 : ℤ), (597599308098350883255532322094667566717507237919138815064871 : ℤ), (1007516983042222219763525434586952427885032074464181776518883 : ℤ)⟩ = ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgB, mMgBa, mMgBb, mMgBc, mMgBd, mMgBe]
  exact mMgBf

theorem mdMgBa : dAdd ONE ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(199 : ℤ), (897296747311466790338673636702778760831452084881866884671584 : ℤ), (1003747365822522651463036787472734152896537054907692588606256 : ℤ)⟩ := by rfl
theorem mdMgBb : dInv ⟨(199 : ℤ), (897296747311466790338673636702778760831452084881866884671584 : ℤ), (1003747365822522651463036787472734152896537054907692588606256 : ℤ)⟩ = ⟨(200 : ℤ), (1286304684830170941342517506454826698201769643860349870948120 : ℤ), (1438905181493189026736312621775226642051129266033071907849953 : ℤ)⟩ := by rfl
theorem mdMgBc : dSub ⟨(200 : ℤ), (1286304684830170941342517506454826698201769643860349870948120 : ℤ), (1438905181493189026736312621775226642051129266033071907849953 : ℤ)⟩ ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ = ⟨(198 : ℤ), (-925689249561785552021279507227402088047788219981020906129870 : ℤ), (1252687515080755180645635970246739268006285976168705803561143 : ℤ)⟩ := by rfl
theorem mdMgBd : dMul (dInt 2) ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(201 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ := by rfl
theorem mdMgBe : dInv ⟨(201 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ = ⟨(197 : ℤ), (402915798094975050026934694955562331709873555089728989301925 : ℤ), (860036929742392795437379837437597272213734286725855694251293 : ℤ)⟩ := by rfl
theorem mdMgBf : dMul ⟨(198 : ℤ), (-925689249561785552021279507227402088047788219981020906129870 : ℤ), (1252687515080755180645635970246739268006285976168705803561143 : ℤ)⟩ ⟨(197 : ℤ), (402915798094975050026934694955562331709873555089728989301925 : ℤ), (860036929742392795437379837437597272213734286725855694251293 : ℤ)⟩ = ⟨(196 : ℤ), (-990862022257711707423064805232835579318088075241941426375120 : ℤ), (1340882466807839542219022411587568971173126904205156417401523 : ℤ)⟩ := by rfl

theorem md_MgB : dMatanD ⟨(202 : ℤ), (750621801455773220541540724257579676562804703923763736167169 : ℤ), (1602226749544220109536445930417222813083484464130369367644537 : ℤ)⟩ ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ = ⟨(196 : ℤ), (-990862022257711707423064805232835579318088075241941426375120 : ℤ), (1340882466807839542219022411587568971173126904205156417401523 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgBa, mdMgBb, mdMgBc, mdMgBd, mdMgBe]
  exact mdMgBf

theorem BMgB_gates : (dLoBig JGB.value = true ∧
    dLoGt (dInv JGB.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGB.value)) ONE) = true ∧
    dLoBig (dInv JGB.value) = true ∧
    dLoBig (dAdd ONE JGB.value) = true ∧
    dLoBig (dMul (dInt 2) JGB.value) = true) := by
  rw [ev_GB, sqi_MgB]
  decide
theorem BMgB_hbig : dLoBig JGB.value = true := BMgB_gates.1
theorem BMgB_hR1 : dLoGt (dInv JGB.value) ONE = true :=
  BMgB_gates.2.1
theorem BMgB_hRden : dLoBig (dAdd (dSqrt (dInv JGB.value)) ONE) = true :=
  BMgB_gates.2.2.1
theorem BMgB_hRbig : dLoBig (dInv JGB.value) = true :=
  BMgB_gates.2.2.2.1
theorem BMgB_hden1 : dLoBig (dAdd ONE JGB.value) = true :=
  BMgB_gates.2.2.2.2.1
theorem BMgB_hden2 : dLoBig (dMul (dInt 2) JGB.value) = true :=
  BMgB_gates.2.2.2.2.2

def JMgB : DCJet := DCJetKit.matanMir JGB (DCJetKit.dMatanTight JGB.value)
theorem JMgB_mem : JetMem JMgB fMgB D :=
  DCJetKit.matanMir_mem (JGB_mem) (DCJetKit.dMatanTight JGB.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGB_mem.2.1 x hx) BMgB_hbig BMgB_hR1 BMgB_hRden BMgB_hRbig)
    BMgB_hbig BMgB_hden1 BMgB_hden2

theorem ev_MgB : (JMgB).value = ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ := by
  rw [show (JMgB).value = dMatanMir (JGB).value (DCJetKit.dMatanTight (JGB).value) from rfl, ev_GB, mt_MgB]
  exact mv_MgB

theorem p0_MgB : (JMgB).part 0 = ⟨(195 : ℤ), (-1346637922318655304531398592357844391712677436021784455916096 : ℤ), (995115088747601509662288532605185202009272149184802936920821 : ℤ)⟩ := by
  rw [show (JMgB).part 0 = DCJetKit.matanSlot (JGB).value (dMatanMir (JGB).value (DCJetKit.dMatanTight (JGB).value)) ((JGB).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_GB, mt_MgB, mv_MgB, md_MgB, p0_GB]
  rfl

theorem p1_MgB : (JMgB).part 1 = ⟨(195 : ℤ), (-1086972999077440198878820883335479654520748490538568902768417 : ℤ), (803232416461861087495298883355326662780366639796596527570643 : ℤ)⟩ := by
  rw [show (JMgB).part 1 = DCJetKit.matanSlot (JGB).value (dMatanMir (JGB).value (DCJetKit.dMatanTight (JGB).value)) ((JGB).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_GB, mt_MgB, mv_MgB, md_MgB, p1_GB]
  rfl

theorem p2_MgB : (JMgB).part 2 = ⟨(196 : ℤ), (-1579284964608097488131919656398265533971602488111035831547008 : ℤ), (1167032556908685159040952623964808336044554202080774863265132 : ℤ)⟩ := by
  rw [show (JMgB).part 2 = DCJetKit.matanSlot (JGB).value (dMatanMir (JGB).value (DCJetKit.dMatanTight (JGB).value)) ((JGB).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_GB, mt_MgB, mv_MgB, md_MgB, p2_GB]
  rfl

/-- literal square root `dSqrt ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgC : dSqrt ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(201 : ℤ), (1475726705435738642498770548906175715089899986940790979812553 : ℤ), (2074451431859940028629624283656781563571077004924601225105236 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1475726705435738642498770548906175715089899986940790979812553 : ℤ)) (rhi := (2074451431859940028629624283656781563571077004924601225105235 : ℤ))
    (nlo := 2177769309136219327461635421943375451909989016484824682736316111240581060291761059373031641047812273080497919749508825088) (nhi := 4303348743145755407669306981287839887439888425058772927791331230155791879570073530725567264642513962818504725792387235840) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgC : dSqrt (dInv ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩) = ⟨(199 : ℤ), (1244786857107413542581605005519252144661261559760453676584474 : ℤ), (1749815781320055624039542327917597907910323427484776522081126 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩)) (K := (199 : ℤ))
    (rlo := (1244786857107413542581605005519252144661261559760453676584474 : ℤ)) (rhi := (1749815781320055624039542327917597907910323427484776522081125 : ℤ))
    (nlo := 1549494319627352381150321190801485332000571439801639916237565267928150478984883558395675960149638185642299281911381491712) (nhi := 3061855268556716724586823869294720238621859766145551235342811035056957429650240813217959798326276116371457126911438749696) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem u9_MgC : dMatanU9 (dInv ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩) = ⟨(200 : ℤ), (708723092797979281714264928075142448704762330707156701401613 : ℤ), (1212999400921505544079159782487997907611901107749923409195097 : ℤ)⟩ := by
  unfold dMatanU9
  rw [sqi_MgC]
  rfl

theorem mt_MgC : DCJetKit.dMatanTight ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(200 : ℤ), (708723092797979281714264928075142448704762330707156701401613 : ℤ), (1212999400921505544079159782487997907611901107749923409195097 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_neg (by decide)]
  exact u9_MgC

theorem mMgCa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgCb : dInv ⟨(201 : ℤ), (1475726705435738642498770548906175715089899986940790979812553 : ℤ), (2074451431859940028629624283656781563571077004924601225105236 : ℤ)⟩ = ⟨(198 : ℤ), (622393428553706771290802502759626072330630779880226838292237 : ℤ), (874907890660027812019771163958798953955161713742388261040563 : ℤ)⟩ := by rfl
theorem mMgCc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(198 : ℤ), (622393428553706771290802502759626072330630779880226838292237 : ℤ), (874907890660027812019771163958798953955161713742388261040563 : ℤ)⟩ = ⟨(198 : ℤ), (977653311393264272473193226518967815286068856939364731720359 : ℤ), (1374302100932787208851514735329213919689348055562493939507327 : ℤ)⟩ := by rfl
theorem mMgCd : dInv ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(197 : ℤ), (482126341200003449928735193510178461113097531734341593721981 : ℤ), (952698605741403859552909210006587661239732643224847349371348 : ℤ)⟩ := by rfl
theorem mMgCe : dMul ⟨(200 : ℤ), (708723092797979281714264928075142448704762330707156701401613 : ℤ), (1212999400921505544079159782487997907611901107749923409195097 : ℤ)⟩ ⟨(197 : ℤ), (482126341200003449928735193510178461113097531734341593721981 : ℤ), (952698605741403859552909210006587661239732643224847349371348 : ℤ)⟩ = ⟨(198 : ℤ), (425273485652281212996881746200530959936035706516175230381665 : ℤ), (1438291715292571292183409499765720035438539505797197482430378 : ℤ)⟩ := by rfl
theorem mMgCf : dSub ⟨(198 : ℤ), (977653311393264272473193226518967815286068856939364731720359 : ℤ), (1374302100932787208851514735329213919689348055562493939507327 : ℤ)⟩ ⟨(198 : ℤ), (425273485652281212996881746200530959936035706516175230381665 : ℤ), (1438291715292571292183409499765720035438539505797197482430378 : ℤ)⟩ = ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ := by rfl

theorem mv_MgC : dMatanMir ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ ⟨(200 : ℤ), (708723092797979281714264928075142448704762330707156701401613 : ℤ), (1212999400921505544079159782487997907611901107749923409195097 : ℤ)⟩ = ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgC, mMgCa, mMgCb, mMgCc, mMgCd, mMgCe]
  exact mMgCf

theorem mdMgCa : dAdd ONE ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(199 : ℤ), (972872668159642594389130242973165994815205655521169314809792 : ℤ), (1138216584311502363055234277856693661551835494513816511774075 : ℤ)⟩ := by rfl
theorem mdMgCb : dInv ⟨(199 : ℤ), (972872668159642594389130242973165994815205655521169314809792 : ℤ), (1138216584311502363055234277856693661551835494513816511774075 : ℤ)⟩ = ⟨(200 : ℤ), (1134340297654725272918475450878578341581939293155379989716419 : ℤ), (1327126335541773492952041157374506103621201760890999539096429 : ℤ)⟩ := by rfl
theorem mdMgCc : dSub ⟨(200 : ℤ), (1134340297654725272918475450878578341581939293155379989716419 : ℤ), (1327126335541773492952041157374506103621201760890999539096429 : ℤ)⟩ ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ = ⟨(199 : ℤ), (-1330887081733649355250028252818076748715655051514947423393115 : ℤ), (1584839975569500785896453125180757492115542178161165270968253 : ℤ)⟩ := by rfl
theorem mdMgCd : dMul (dInt 2) ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(200 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ := by rfl
theorem mdMgCe : dInv ⟨(200 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ = ⟨(198 : ℤ), (482126341200003449928735193510178461113097531734341593721981 : ℤ), (952698605741403859552909210006587661239732643224847349371348 : ℤ)⟩ := by rfl
theorem mdMgCf : dMul ⟨(199 : ℤ), (-1330887081733649355250028252818076748715655051514947423393115 : ℤ), (1584839975569500785896453125180757492115542178161165270968253 : ℤ)⟩ ⟨(198 : ℤ), (482126341200003449928735193510178461113097531734341593721981 : ℤ), (952698605741403859552909210006587661239732643224847349371348 : ℤ)⟩ = ⟨(197 : ℤ), (-789037431590324909571801012600450019188846145628765235570567 : ℤ), (939597416616366673127898286918501068496402198930865951348204 : ℤ)⟩ := by rfl

theorem md_MgC : dMatanD ⟨(201 : ℤ), (677614584120589826472596787210338774216416634519091588636419 : ℤ), (1338990248728028901137012926744449441162935990489680376493545 : ℤ)⟩ ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ = ⟨(197 : ℤ), (-789037431590324909571801012600450019188846145628765235570567 : ℤ), (939597416616366673127898286918501068496402198930865951348204 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgCa, mdMgCb, mdMgCc, mdMgCd, mdMgCe]
  exact mdMgCf

theorem BMgC_gates : (dLoBig JGC.value = true ∧
    dLoGt (dInv JGC.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGC.value)) ONE) = true ∧
    dLoBig (dInv JGC.value) = true ∧
    dLoBig (dAdd ONE JGC.value) = true ∧
    dLoBig (dMul (dInt 2) JGC.value) = true) := by
  rw [ev_GC, sqi_MgC]
  decide
theorem BMgC_hbig : dLoBig JGC.value = true := BMgC_gates.1
theorem BMgC_hR1 : dLoGt (dInv JGC.value) ONE = true :=
  BMgC_gates.2.1
theorem BMgC_hRden : dLoBig (dAdd (dSqrt (dInv JGC.value)) ONE) = true :=
  BMgC_gates.2.2.1
theorem BMgC_hRbig : dLoBig (dInv JGC.value) = true :=
  BMgC_gates.2.2.2.1
theorem BMgC_hden1 : dLoBig (dAdd ONE JGC.value) = true :=
  BMgC_gates.2.2.2.2.1
theorem BMgC_hden2 : dLoBig (dMul (dInt 2) JGC.value) = true :=
  BMgC_gates.2.2.2.2.2

def JMgC : DCJet := DCJetKit.matanMir JGC (DCJetKit.dMatanTight JGC.value)
theorem JMgC_mem : JetMem JMgC fMgC D :=
  DCJetKit.matanMir_mem (JGC_mem) (DCJetKit.dMatanTight JGC.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGC_mem.2.1 x hx) BMgC_hbig BMgC_hR1 BMgC_hRden BMgC_hRbig)
    BMgC_hbig BMgC_hden1 BMgC_hden2

theorem ev_MgC : (JMgC).value = ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ := by
  rw [show (JMgC).value = dMatanMir (JGC).value (DCJetKit.dMatanTight (JGC).value) from rfl, ev_GC, mt_MgC]
  exact mv_MgC

theorem p0_MgC : (JMgC).part 0 = ⟨(196 : ℤ), (-1033459738337783812469085644590579657706812238432081250609606 : ℤ), (867859365265788030320188975564623081592529009463089903131454 : ℤ)⟩ := by
  rw [show (JMgC).part 0 = DCJetKit.matanSlot (JGC).value (dMatanMir (JGC).value (DCJetKit.dMatanTight (JGC).value)) ((JGC).part 0) from rfl, DCJetKit.matanSlot_eq,
    ev_GC, mt_MgC, mv_MgC, md_MgC, p0_GC]
  rfl

theorem p1_MgC : (JMgC).part 1 = ⟨(196 : ℤ), (-1404218959623297817342583113945194322819646659153474622411103 : ℤ), (1179208564963507953912945083193472292937287625874180056098735 : ℤ)⟩ := by
  rw [show (JMgC).part 1 = DCJetKit.matanSlot (JGC).value (dMatanMir (JGC).value (DCJetKit.dMatanTight (JGC).value)) ((JGC).part 1) from rfl, DCJetKit.matanSlot_eq,
    ev_GC, mt_MgC, mv_MgC, md_MgC, p1_GC]
  rfl

theorem p2_MgC : (JMgC).part 2 = ⟨(196 : ℤ), (-1441639347149858036626851505107372959180630243265055163881261 : ℤ), (1210632753601020005103353418889154334425370455585242204009237 : ℤ)⟩ := by
  rw [show (JMgC).part 2 = DCJetKit.matanSlot (JGC).value (dMatanMir (JGC).value (DCJetKit.dMatanTight (JGC).value)) ((JGC).part 2) from rfl, DCJetKit.matanSlot_eq,
    ev_GC, mt_MgC, mv_MgC, md_MgC, p2_GC]
  rfl

def JDihA : DCJet := DCJetKit.mul JWA JMgA
theorem JDihA_mem : JetMem JDihA fDihA D :=
  DCJetKit.mul_mem (JWA_mem) (JMgA_mem)

theorem op_DihA : dMul ⟨(202 : ℤ), (805674715705732506325785719279213913857658278551759208058092 : ℤ), (924221404684847268124964401432519966721484197636067322064598 : ℤ)⟩ ⟨(197 : ℤ), (-441533602725791207801705027129995155894479361309607349021627 : ℤ), (626548579112138461932576141983547679199205521530256267471219 : ℤ)⟩ = ⟨(201 : ℤ), (-1015782302210582610644663206240626689612608308811894124311973 : ℤ), (1441423606738598295857566092513668191909375071544569415351232 : ℤ)⟩ := by
  rfl

theorem ev_DihA : (JDihA).value = ⟨(201 : ℤ), (-1015782302210582610644663206240626689612608308811894124311973 : ℤ), (1441423606738598295857566092513668191909375071544569415351232 : ℤ)⟩ := by
  rw [show (JDihA).value = dMul (JWA).value (JMgA).value from rfl, ev_WA, ev_MgA]
  exact op_DihA

theorem p0_DihA : (JDihA).part 0 = ⟨(197 : ℤ), (-817139627645384859323124958761013812791601177266610454741463 : ℤ), (605677582016483903117218821758948370912852599890077640633120 : ℤ)⟩ := by
  rw [show (JDihA).part 0 = dAdd (dMul (JWA).value ((JMgA).part 0)) (dMul (JMgA).value ((JWA).part 0)) from rfl, ev_WA, ev_MgA, p0_WA, p0_MgA]
  rfl

theorem p1_DihA : (JDihA).part 1 = ⟨(198 : ℤ), (-913535001266166966990395280106745394243864574942466063668118 : ℤ), (710586670852308734215203285283569440559107952749026734918906 : ℤ)⟩ := by
  rw [show (JDihA).part 1 = dAdd (dMul (JWA).value ((JMgA).part 1)) (dMul (JMgA).value ((JWA).part 1)) from rfl, ev_WA, ev_MgA, p1_WA, p1_MgA]
  rfl

theorem p2_DihA : (JDihA).part 2 = ⟨(198 : ℤ), (-1369820922501869893021532482865304975885114632044233887226785 : ℤ), (1014742972745253100863295606928847784615093743229666338360074 : ℤ)⟩ := by
  rw [show (JDihA).part 2 = dAdd (dMul (JWA).value ((JMgA).part 2)) (dMul (JMgA).value ((JWA).part 2)) from rfl, ev_WA, ev_MgA, p2_WA, p2_MgA]
  rfl

def JDihB : DCJet := DCJetKit.mul JWB JMgB
theorem JDihB_mem : JetMem JDihB fDihB D :=
  DCJetKit.mul_mem (JWB_mem) (JMgB_mem)

theorem op_DihB : dMul ⟨(202 : ℤ), (824778604998167072925775170681264149506537821507188542539185 : ℤ), (957229378491220675534825900697903711677715805676017971467802 : ℤ)⟩ ⟨(197 : ℤ), (-446480609853728961980778907401466303746751829830218913299327 : ℤ), (623632710384664143678454441920554381299115315473054186933450 : ℤ)⟩ = ⟨(201 : ℤ), (-1063847752452077975465322269781791443316627190507030710183228 : ℤ), (1485955364367726632671185134387095756967479095578446780106521 : ℤ)⟩ := by
  rfl

theorem ev_DihB : (JDihB).value = ⟨(201 : ℤ), (-1063847752452077975465322269781791443316627190507030710183228 : ℤ), (1485955364367726632671185134387095756967479095578446780106521 : ℤ)⟩ := by
  rw [show (JDihB).value = dMul (JWB).value (JMgB).value from rfl, ev_WB, ev_MgB]
  exact op_DihB

theorem p0_DihB : (JDihB).part 0 = ⟨(197 : ℤ), (-884293477019883862235837411407104945213245127381410541240416 : ℤ), (651568789543542232490269008368943595494689409567445877516118 : ℤ)⟩ := by
  rw [show (JDihB).part 0 = dAdd (dMul (JWB).value ((JMgB).part 0)) (dMul (JMgB).value ((JWB).part 0)) from rfl, ev_WB, ev_MgB, p0_WB, p0_MgB]
  rfl

theorem p1_DihB : (JDihB).part 1 = ⟨(198 : ℤ), (-1446468311335952560735341382819729488217355172833656865555099 : ℤ), (1065397806643291264885649926598818052797929721684946918284145 : ℤ)⟩ := by
  rw [show (JDihB).part 1 = dAdd (dMul (JWB).value ((JMgB).part 1)) (dMul (JMgB).value ((JWB).part 1)) from rfl, ev_WB, ev_MgB, p1_WB, p1_MgB]
  rfl

theorem p2_DihB : (JDihB).part 2 = ⟨(198 : ℤ), (-992893021841155049988060169516023366643725159368844618716865 : ℤ), (768006623771205575244177314074208380380041782235978146123443 : ℤ)⟩ := by
  rw [show (JDihB).part 2 = dAdd (dMul (JWB).value ((JMgB).part 2)) (dMul (JMgB).value ((JWB).part 2)) from rfl, ev_WB, ev_MgB, p2_WB, p2_MgB]
  rfl

def JDihC : DCJet := DCJetKit.mul JWC JMgC
theorem JDihC_mem : JetMem JDihC fDihC D :=
  DCJetKit.mul_mem (JWC_mem) (JMgC_mem)

theorem op_DihC : dMul ⟨(202 : ℤ), (1108238337642097343538551764911881648749624233701524602816524 : ℤ), (1237535696845183924464798313125615092832121940193097077440295 : ℤ)⟩ ⟨(198 : ℤ), (-460638403899307019710216273246752220152470648857832750710019 : ℤ), (949028615280505995854632989128682959753312349046318709125662 : ℤ)⟩ = ⟨(201 : ℤ), (-709494022124609272588572335351235171406713056651246288396128 : ℤ), (1461732507899842465624637272289933830125317106250784804573663 : ℤ)⟩ := by
  rfl

theorem ev_DihC : (JDihC).value = ⟨(201 : ℤ), (-709494022124609272588572335351235171406713056651246288396128 : ℤ), (1461732507899842465624637272289933830125317106250784804573663 : ℤ)⟩ := by
  rw [show (JDihC).value = dMul (JWC).value (JMgC).value from rfl, ev_WC, ev_MgC]
  exact op_DihC

theorem p0_DihC : (JDihC).part 0 = ⟨(198 : ℤ), (-869127468681833206888038045242548059073517834799167231526723 : ℤ), (819246730611999166693971983059723994627369458666447131169159 : ℤ)⟩ := by
  rw [show (JDihC).part 0 = dAdd (dMul (JWC).value ((JMgC).part 0)) (dMul (JMgC).value ((JWC).part 0)) from rfl, ev_WC, ev_MgC, p0_WC, p0_MgC]
  rfl

theorem p1_DihC : (JDihC).part 1 = ⟨(198 : ℤ), (-1287456959734373200533452083959863180391942969044855263167331 : ℤ), (1008139661242421328559540968203167262020349816350590577601580 : ℤ)⟩ := by
  rw [show (JDihC).part 1 = dAdd (dMul (JWC).value ((JMgC).part 1)) (dMul (JMgC).value ((JWC).part 1)) from rfl, ev_WC, ev_MgC, p1_WC, p1_MgC]
  rfl

theorem p2_DihC : (JDihC).part 2 = ⟨(198 : ℤ), (-1319111726706130128681646345237567721038384665051690151101111 : ℤ), (1033716877090200351321578329571982217692570389107345748998103 : ℤ)⟩ := by
  rw [show (JDihC).part 2 = dAdd (dMul (JWC).value ((JMgC).part 2)) (dMul (JMgC).value ((JWC).part 2)) from rfl, ev_WC, ev_MgC, p2_WC, p2_MgC]
  rfl

def JSeA : DCJet := DCJetKit.mul JMtA JIA
theorem JSeA_mem : JetMem JSeA fSeA D :=
  DCJetKit.mul_mem (JMtA_mem) (JIA_mem)

theorem op_SeA : dMul ⟨(200 : ℤ), (1604730203322641142879714480343472727742261688946434233401245 : ℤ), (1605641925430842680491493087066587169276228384457797001590987 : ℤ)⟩ ⟨(204 : ℤ), (950971194194127044127820492995137417411365456285590905643958 : ℤ), (985448365873131863982169256768428950053449540701194478328512 : ℤ)⟩ = ⟨(204 : ℤ), (949664614180459620615254429007148628356612274252590329376817 : ℤ), (984653526155609070420081716396076040981738547672180936241899 : ℤ)⟩ := by
  rfl

theorem ev_SeA : (JSeA).value = ⟨(204 : ℤ), (949664614180459620615254429007148628356612274252590329376817 : ℤ), (984653526155609070420081716396076040981738547672180936241899 : ℤ)⟩ := by
  rw [show (JSeA).value = dMul (JMtA).value (JIA).value from rfl, ev_MtA, ev_IA]
  exact op_SeA

theorem p0_SeA : (JSeA).part 0 = ⟨(205 : ℤ), (-1158665799793197323127528055296525655745982357000376078947517 : ℤ), (-1020969974815207961633955998514489596542238374322909300720766 : ℤ)⟩ := by
  rw [show (JSeA).part 0 = dAdd (dMul (JMtA).value ((JIA).part 0)) (dMul (JIA).value ((JMtA).part 0)) from rfl, ev_MtA, ev_IA, p0_MtA, p0_IA]
  rfl

theorem p1_SeA : (JSeA).part 1 = ⟨(205 : ℤ), (-1196034391019421427822300433558958898813454254236967223621813 : ℤ), (-1069633493693328297810428579451682932853724870869214848654032 : ℤ)⟩ := by
  rw [show (JSeA).part 1 = dAdd (dMul (JMtA).value ((JIA).part 1)) (dMul (JIA).value ((JMtA).part 1)) from rfl, ev_MtA, ev_IA, p1_MtA, p1_IA]
  rfl

theorem p2_SeA : (JSeA).part 2 = ⟨(207 : ℤ), (922201249731282997112142506904171186214881231415967292737487 : ℤ), (1109673378922175748788208665248248669229728667995770284601120 : ℤ)⟩ := by
  rw [show (JSeA).part 2 = dAdd (dMul (JMtA).value ((JIA).part 2)) (dMul (JIA).value ((JMtA).part 2)) from rfl, ev_MtA, ev_IA, p2_MtA, p2_IA]
  rfl

def JSeB : DCJet := DCJetKit.mul JMtB JIB
theorem JSeB_mem : JetMem JSeB fSeB D :=
  DCJetKit.mul_mem (JMtB_mem) (JIB_mem)

theorem op_SeB : dMul ⟨(200 : ℤ), (1603917347830861521883745325722975129271067219867434998704289 : ℤ), (1605269074625382975530986098186848528785278927018903761838548 : ℤ)⟩ ⟨(204 : ℤ), (1079611128443189150836564483201376003437953269838744337469864 : ℤ), (1152906935643606595975083348888388424918997760052031395927874 : ℤ)⟩ = ⟨(204 : ℤ), (1077581692715341767547685761839501772214937275503599053331212 : ℤ), (1151709523787661820616063205722321896173878677365813301026575 : ℤ)⟩ := by
  rfl

theorem ev_SeB : (JSeB).value = ⟨(204 : ℤ), (1077581692715341767547685761839501772214937275503599053331212 : ℤ), (1151709523787661820616063205722321896173878677365813301026575 : ℤ)⟩ := by
  rw [show (JSeB).value = dMul (JMtB).value (JIB).value from rfl, ev_MtB, ev_IB]
  exact op_SeB

theorem p0_SeB : (JSeB).part 0 = ⟨(206 : ℤ), (653564045152565714882278504845647443181732467872220606602661 : ℤ), (848762979701911865032340129012225268046756259737149721255168 : ℤ)⟩ := by
  rw [show (JSeB).part 0 = dAdd (dMul (JMtB).value ((JIB).part 0)) (dMul (JIB).value ((JMtB).part 0)) from rfl, ev_MtB, ev_IB, p0_MtB, p0_IB]
  rfl

theorem p1_SeB : (JSeB).part 1 = ⟨(205 : ℤ), (-1532464264292849135791826121127553676142961944830835008494537 : ℤ), (-1241028675446347680617309661576824256734715115136548973536250 : ℤ)⟩ := by
  rw [show (JSeB).part 1 = dAdd (dMul (JMtB).value ((JIB).part 1)) (dMul (JIB).value ((JMtB).part 1)) from rfl, ev_MtB, ev_IB, p1_MtB, p1_IB]
  rfl

theorem p2_SeB : (JSeB).part 2 = ⟨(205 : ℤ), (-1524603819291835143915808764671896369422984196726217189802445 : ℤ), (-1234469111071362547541847460189461318500828776823072019548531 : ℤ)⟩ := by
  rw [show (JSeB).part 2 = dAdd (dMul (JMtB).value ((JIB).part 2)) (dMul (JIB).value ((JMtB).part 2)) from rfl, ev_MtB, ev_IB, p2_MtB, p2_IB]
  rfl

def JSeC : DCJet := DCJetKit.mul JMtC JIC
theorem JSeC_mem : JetMem JSeC fSeC D :=
  DCJetKit.mul_mem (JMtC_mem) (JIC_mem)

theorem op_SeC : dMul ⟨(200 : ℤ), (1604811718214045392090808563178259044727923678252804556964385 : ℤ), (1605696623234591478782933069388591805028820262585086826493200 : ℤ)⟩ ⟨(204 : ℤ), (930646259780262330129504379471157488711068087944508642585160 : ℤ), (967055948054933861789239919713877404474162541868495935751340 : ℤ)⟩ = ⟨(204 : ℤ), (929414813808918844264521335601285641438473575899496442447631 : ℤ), (966308860393418632181838273017060925572497585563332241658688 : ℤ)⟩ := by
  rfl

theorem ev_SeC : (JSeC).value = ⟨(204 : ℤ), (929414813808918844264521335601285641438473575899496442447631 : ℤ), (966308860393418632181838273017060925572497585563332241658688 : ℤ)⟩ := by
  rw [show (JSeC).value = dMul (JMtC).value (JIC).value from rfl, ev_MtC, ev_IC]
  exact op_SeC

theorem p0_SeC : (JSeC).part 0 = ⟨(205 : ℤ), (-1130623102147822225347745359857720788375520341979675293250793 : ℤ), (-988488731267971012072688327590838649787944191971835563522711 : ℤ)⟩ := by
  rw [show (JSeC).part 0 = dAdd (dMul (JMtC).value ((JIC).part 0)) (dMul (JIC).value ((JMtC).part 0)) from rfl, ev_MtC, ev_IC, p0_MtC, p0_IC]
  rfl

theorem p1_SeC : (JSeC).part 1 = ⟨(207 : ℤ), (873197604152896879838212639852663594475098356864324247765899 : ℤ), (1051156318681311782476696784900733121054722243901152010832646 : ℤ)⟩ := by
  rw [show (JSeC).part 1 = dAdd (dMul (JMtC).value ((JIC).part 1)) (dMul (JIC).value ((JMtC).part 1)) from rfl, ev_MtC, ev_IC, p1_MtC, p1_IC]
  rfl

theorem p2_SeC : (JSeC).part 2 = ⟨(205 : ℤ), (-1161016646155709486001515430052655769123864323977892361933367 : ℤ), (-1030442299256456252215658331424242664764439074057968247392358 : ℤ)⟩ := by
  rw [show (JSeC).part 2 = dAdd (dMul (JMtC).value ((JIC).part 2)) (dMul (JIC).value ((JMtC).part 2)) from rfl, ev_MtC, ev_IC, p2_MtC, p2_IC]
  rfl

def JSe1 : DCJet := DCJetKit.add JSeA JSeB
theorem JSe1_mem : JetMem JSe1 fSe1 D :=
  DCJetKit.add_mem (JSeA_mem) (JSeB_mem)

theorem op_Se1 : dAdd ⟨(204 : ℤ), (949664614180459620615254429007148628356612274252590329376817 : ℤ), (984653526155609070420081716396076040981738547672180936241899 : ℤ)⟩ ⟨(204 : ℤ), (1077581692715341767547685761839501772214937275503599053331212 : ℤ), (1151709523787661820616063205722321896173878677365813301026575 : ℤ)⟩ = ⟨(203 : ℤ), (1013623153447900694081470095423325200285774774878094691354014 : ℤ), (1068181524971635445518072461059198968577808612518997118634237 : ℤ)⟩ := by
  rfl

theorem ev_Se1 : (JSe1).value = ⟨(203 : ℤ), (1013623153447900694081470095423325200285774774878094691354014 : ℤ), (1068181524971635445518072461059198968577808612518997118634237 : ℤ)⟩ := by
  rw [show (JSe1).value = dAdd (JSeA).value (JSeB).value from rfl, ev_SeA, ev_SeB]
  exact op_Se1

theorem p0_Se1 : (JSe1).part 0 = ⟨(205 : ℤ), (-831883777216914465686388802873701934155116123064265775646187 : ℤ), (-596588484964252029117785934008376962518860244454334440093182 : ℤ)⟩ := by
  rw [show (JSe1).part 0 = dAdd ((JSeA).part 0) ((JSeB).part 0) from rfl, p0_SeA, p0_SeB]
  rfl

theorem p1_Se1 : (JSe1).part 1 = ⟨(204 : ℤ), (-1364249327656135281807063277343256287478208099533901116058175 : ℤ), (-1155331084569837989213869120514253594794219993002881911095141 : ℤ)⟩ := by
  rw [show (JSe1).part 1 = dAdd ((JSeA).part 1) ((JSeB).part 1) from rfl, p1_SeA, p1_SeB]
  rfl

theorem p2_Se1 : (JSe1).part 2 = ⟨(205 : ℤ), (-1294053506859014394637773137945853572869263888872225366618074 : ℤ), (-957050766340818610344795293877399151193396609824129448398251 : ℤ)⟩ := by
  rw [show (JSe1).part 2 = dAdd ((JSeA).part 2) ((JSeB).part 2) from rfl, p2_SeA, p2_SeB]
  rfl

def JSe : DCJet := DCJetKit.add JSe1 JSeC
theorem JSe_mem : JetMem JSe fSe D :=
  DCJetKit.add_mem (JSe1_mem) (JSeC_mem)

theorem op_Se : dAdd ⟨(203 : ℤ), (1013623153447900694081470095423325200285774774878094691354014 : ℤ), (1068181524971635445518072461059198968577808612518997118634237 : ℤ)⟩ ⟨(204 : ℤ), (929414813808918844264521335601285641438473575899496442447631 : ℤ), (966308860393418632181838273017060925572497585563332241658688 : ℤ)⟩ = ⟨(203 : ℤ), (1478330560352360116213730763223968021005011562827842912577829 : ℤ), (1551335955168344761608991597567729431364057405300663239463581 : ℤ)⟩ := by
  rfl

theorem ev_Se : (JSe).value = ⟨(203 : ℤ), (1478330560352360116213730763223968021005011562827842912577829 : ℤ), (1551335955168344761608991597567729431364057405300663239463581 : ℤ)⟩ := by
  rw [show (JSe).value = dAdd (JSe1).value (JSeC).value from rfl, ev_Se1, ev_SeC]
  exact op_Se

theorem p0_Se : (JSe).part 0 = ⟨(204 : ℤ), (-981253439682368345517067081365711361265318232521970534448490 : ℤ), (-792538608116111520595237130799607806153402218213085001807946 : ℤ)⟩ := by
  rw [show (JSe).part 0 = dAdd ((JSe1).part 0) ((JSeC).part 0) from rfl, p0_Se1, p0_SeC]
  rfl

theorem p1_Se : (JSe).part 1 = ⟨(204 : ℤ), (-1255099627137023171827286697361673338168820804925860585087438 : ℤ), (-1023936544734674016404282022401661954662379712515237909741060 : ℤ)⟩ := by
  rw [show (JSe).part 1 = dAdd ((JSe1).part 1) ((JSeC).part 1) from rfl, p1_Se1, p1_SeC]
  rfl

theorem p2_Se : (JSe).part 2 = ⟨(204 : ℤ), (-1227535076507361940319644283999254670996564106425058864275721 : ℤ), (-993746532798637431280226812650820907978917841941048847895304 : ℤ)⟩ := by
  rw [show (JSe).part 2 = dAdd ((JSe1).part 2) ((JSeC).part 2) from rfl, p2_Se1, p2_SeC]
  rfl

def JK1Se : DCJet := DCJetKit.mul JK1 JSe
theorem JK1Se_mem : JetMem JK1Se fK1Se D :=
  DCJetKit.mul_mem (JK1_mem) (JSe_mem)

theorem op_K1Se : dMul ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ ⟨(203 : ℤ), (1478330560352360116213730763223968021005011562827842912577829 : ℤ), (1551335955168344761608991597567729431364057405300663239463581 : ℤ)⟩ = ⟨(203 : ℤ), (952504122058002130437401271732978824170996434018714009005036 : ℤ), (999542374098279269056336202224273925410321257480138361666970 : ℤ)⟩ := by
  rfl

theorem ev_K1Se : (JK1Se).value = ⟨(203 : ℤ), (952504122058002130437401271732978824170996434018714009005036 : ℤ), (999542374098279269056336202224273925410321257480138361666970 : ℤ)⟩ := by
  rw [show (JK1Se).value = dMul (JK1).value (JSe).value from rfl, ev_K1, ev_Se]
  exact op_K1Se

theorem p0_K1Se : (JK1Se).part 0 = ⟨(205 : ℤ), (-1264464205093195522883142102828949067797755278851132201239505 : ℤ), (-1021282129134607432926016329460182844462710046756489719776662 : ℤ)⟩ := by
  rw [show (JK1Se).part 0 = dAdd (dMul (JK1).value ((JSe).part 0)) (dMul (JSe).value ((JK1).part 0)) from rfl, ev_K1, ev_Se, p0_K1, p0_Se]
  rfl

theorem p1_K1Se : (JK1Se).part 1 = ⟨(204 : ℤ), (-808674134612105463641194556659493848531937833948132762283462 : ℤ), (-659733219174702864966979887916467911225703133041298000154978 : ℤ)⟩ := by
  rw [show (JK1Se).part 1 = dAdd (dMul (JK1).value ((JSe).part 1)) (dMul (JSe).value ((JK1).part 1)) from rfl, ev_K1, ev_Se, p1_K1, p1_Se]
  rfl

theorem p2_K1Se : (JK1Se).part 2 = ⟨(205 : ℤ), (-1581827998730210831332363507854780675368677770382864413987936 : ℤ), (-1280562946011127729182937820898011995205805788927489132167522 : ℤ)⟩ := by
  rw [show (JK1Se).part 2 = dAdd (dMul (JK1).value ((JSe).part 2)) (dMul (JSe).value ((JK1).part 2)) from rfl, ev_K1, ev_Se, p2_K1, p2_Se]
  rfl

def JFirst : DCJet := DCJetKit.sub JC112 JK1Se
theorem JFirst_mem : JetMem JFirst fFirst D :=
  DCJetKit.sub_mem (JC112_mem D) (JK1Se_mem)

theorem op_First : dAdd ⟨(203 : ℤ), (1071292029505993517027974728227441735014801995855195223534250 : ℤ), (1071292029505993517027974728227441735014801995855195223534251 : ℤ)⟩ (dNeg ⟨(203 : ℤ), (952504122058002130437401271732978824170996434018714009005036 : ℤ), (999542374098279269056336202224273925410321257480138361666970 : ℤ)⟩) = ⟨(203 : ℤ), (71749655407714247971638526003167809604480738375056861867280 : ℤ), (118787907447991386590573456494462910843805561836481214529215 : ℤ)⟩ := by
  rfl

theorem ev_First : (JFirst).value = ⟨(203 : ℤ), (71749655407714247971638526003167809604480738375056861867280 : ℤ), (118787907447991386590573456494462910843805561836481214529215 : ℤ)⟩ := by
  rw [show (JFirst).value = dAdd (JC112).value (dNeg (JK1Se).value) from rfl, ev_C112, ev_K1Se]
  exact op_First

theorem p0_First : (JFirst).part 0 = ⟨(205 : ℤ), (1021282129134607432926016329460182844462710046756489719776662 : ℤ), (1264464205093195522883142102828949067797755278851132201239505 : ℤ)⟩ := by
  rw [show (JFirst).part 0 = dAdd ((JC112).part 0) (dNeg ((JK1Se).part 0)) from rfl, p0_C112, p0_K1Se]
  rfl

theorem p1_First : (JFirst).part 1 = ⟨(204 : ℤ), (659733219174702864966979887916467911225703133041298000154978 : ℤ), (808674134612105463641194556659493848531937833948132762283462 : ℤ)⟩ := by
  rw [show (JFirst).part 1 = dAdd ((JC112).part 1) (dNeg ((JK1Se).part 1)) from rfl, p1_C112, p1_K1Se]
  rfl

theorem p2_First : (JFirst).part 2 = ⟨(205 : ℤ), (1280562946011127729182937820898011995205805788927489132167522 : ℤ), (1581827998730210831332363507854780675368677770382864413987936 : ℤ)⟩ := by
  rw [show (JFirst).part 2 = dAdd ((JC112).part 2) (dNeg ((JK1Se).part 2)) from rfl, p2_C112, p2_K1Se]
  rfl

def JLf5DihA : DCJet := DCJetKit.mul JLf5 JDihA
theorem JLf5DihA_mem : JetMem JLf5DihA fLf5DihA D :=
  DCJetKit.mul_mem (JLf5_mem) (JDihA_mem)

theorem op_Lf5DihA : dMul ⟨(201 : ℤ), (1210160615502477205823858852582960351766127797586212291586922 : ℤ), (1508872985388925262531502271252997022041042263626811679059617 : ℤ)⟩ ⟨(201 : ℤ), (-1015782302210582610644663206240626689612608308811894124311973 : ℤ), (1441423606738598295857566092513668191909375071544569415351232 : ℤ)⟩ = ⟨(202 : ℤ), (-953793134911114304325941424267029160836054864208561929622757 : ℤ), (1353459237884101149018546565831396620663780032472361933820802 : ℤ)⟩ := by
  rfl

theorem ev_Lf5DihA : (JLf5DihA).value = ⟨(202 : ℤ), (-953793134911114304325941424267029160836054864208561929622757 : ℤ), (1353459237884101149018546565831396620663780032472361933820802 : ℤ)⟩ := by
  rw [show (JLf5DihA).value = dMul (JLf5).value (JDihA).value from rfl, ev_Lf5, ev_DihA]
  exact op_Lf5DihA

theorem p0_Lf5DihA : (JLf5DihA).part 0 = ⟨(199 : ℤ), (-1534545670693163843378755914415120183647250285229772568267585 : ℤ), (1137430960235659116420096813735803485073731220524514819727959 : ℤ)⟩ := by
  rw [show (JLf5DihA).part 0 = dAdd (dMul (JLf5).value ((JDihA).part 0)) (dMul (JDihA).value ((JLf5).part 0)) from rfl, ev_Lf5, ev_DihA, p0_Lf5, p0_DihA]
  rfl

theorem p1_Lf5DihA : (JLf5DihA).part 1 = ⟨(199 : ℤ), (-1550777700054993163832484078149835635835769604153465769187821 : ℤ), (1155579259188894310436271623398083506429161876575611604824276 : ℤ)⟩ := by
  rw [show (JLf5DihA).part 1 = dAdd (dMul (JLf5).value ((JDihA).part 1)) (dMul (JDihA).value ((JLf5).part 1)) from rfl, ev_Lf5, ev_DihA, p1_Lf5, p1_DihA]
  rfl

theorem p2_Lf5DihA : (JLf5DihA).part 2 = ⟨(199 : ℤ), (-1286226181630240862155176469281630376486084899725900171085767 : ℤ), (952817231603107450359818119872849689988396135466062223495057 : ℤ)⟩ := by
  rw [show (JLf5DihA).part 2 = dAdd (dMul (JLf5).value ((JDihA).part 2)) (dMul (JDihA).value ((JLf5).part 2)) from rfl, ev_Lf5, ev_DihA, p2_Lf5, p2_DihA]
  rfl

def JLf6DihB : DCJet := DCJetKit.mul JLf6 JDihB
theorem JLf6DihB_mem : JetMem JLf6DihB fLf6DihB D :=
  DCJetKit.mul_mem (JLf6_mem) (JDihB_mem)

theorem op_Lf6DihB : dMul ⟨(201 : ℤ), (1012399259254051501781075630099943786211672633513581041610014 : ℤ), (1355622941088282321506090325080197278331454644339291104089355 : ℤ)⟩ ⟨(201 : ℤ), (-1063847752452077975465322269781791443316627190507030710183228 : ℤ), (1485955364367726632671185134387095756967479095578446780106521 : ℤ)⟩ = ⟨(202 : ℤ), (-897468588911452281756233675514008049722761215315882163315727 : ℤ), (1253561198931592170436251432234293231995313623981117278248879 : ℤ)⟩ := by
  rfl

theorem ev_Lf6DihB : (JLf6DihB).value = ⟨(202 : ℤ), (-897468588911452281756233675514008049722761215315882163315727 : ℤ), (1253561198931592170436251432234293231995313623981117278248879 : ℤ)⟩ := by
  rw [show (JLf6DihB).value = dMul (JLf6).value (JDihB).value from rfl, ev_Lf6, ev_DihB]
  exact op_Lf6DihB

theorem p0_Lf6DihB : (JLf6DihB).part 0 = ⟨(199 : ℤ), (-1491990968022252862773708306196605466969622758457784012410388 : ℤ), (1099334976800126389752448610770016127535361799473327817257137 : ℤ)⟩ := by
  rw [show (JLf6DihB).part 0 = dAdd (dMul (JLf6).value ((JDihB).part 0)) (dMul (JDihB).value ((JLf6).part 0)) from rfl, ev_Lf6, ev_DihB, p0_Lf6, p0_DihB]
  rfl

theorem p1_Lf6DihB : (JLf6DihB).part 1 = ⟨(199 : ℤ), (-1220249675094637581651223152780627880892078822158216832737170 : ℤ), (898776224279876052362011199988071186572125016121708979597715 : ℤ)⟩ := by
  rw [show (JLf6DihB).part 1 = dAdd (dMul (JLf6).value ((JDihB).part 1)) (dMul (JDihB).value ((JLf6).part 1)) from rfl, ev_Lf6, ev_DihB, p1_Lf6, p1_DihB]
  rfl

theorem p2_Lf6DihB : (JLf6DihB).part 2 = ⟨(199 : ℤ), (-1552012353793248398023258598483773229407734046881502776768770 : ℤ), (1159360436054596305942000749355657039528732678631452016602652 : ℤ)⟩ := by
  rw [show (JLf6DihB).part 2 = dAdd (dMul (JLf6).value ((JDihB).part 2)) (dMul (JDihB).value ((JLf6).part 2)) from rfl, ev_Lf6, ev_DihB, p2_Lf6, p2_DihB]
  rfl

def JPosA : DCJet := DCJetKit.add JLf5DihA JLf6DihB
theorem JPosA_mem : JetMem JPosA fPosA D :=
  DCJetKit.add_mem (JLf5DihA_mem) (JLf6DihB_mem)

theorem op_PosA : dAdd ⟨(202 : ℤ), (-953793134911114304325941424267029160836054864208561929622757 : ℤ), (1353459237884101149018546565831396620663780032472361933820802 : ℤ)⟩ ⟨(202 : ℤ), (-897468588911452281756233675514008049722761215315882163315727 : ℤ), (1253561198931592170436251432234293231995313623981117278248879 : ℤ)⟩ = ⟨(201 : ℤ), (-925630861911283293041087549890518605279408039762222046469242 : ℤ), (1303510218407846659727398999032844926329546828226739606034841 : ℤ)⟩ := by
  rfl

theorem ev_PosA : (JPosA).value = ⟨(201 : ℤ), (-925630861911283293041087549890518605279408039762222046469242 : ℤ), (1303510218407846659727398999032844926329546828226739606034841 : ℤ)⟩ := by
  rw [show (JPosA).value = dAdd (JLf5DihA).value (JLf6DihB).value from rfl, ev_Lf5DihA, ev_Lf6DihB]
  exact op_PosA

theorem p0_PosA : (JPosA).part 0 = ⟨(198 : ℤ), (-1513268319357708353076232110305862825308436521843778290338987 : ℤ), (1118382968517892753086272712252909806304546509998921318492548 : ℤ)⟩ := by
  rw [show (JPosA).part 0 = dAdd ((JLf5DihA).part 0) ((JLf6DihB).part 0) from rfl, p0_Lf5DihA, p0_Lf6DihB]
  rfl

theorem p1_PosA : (JPosA).part 1 = ⟨(198 : ℤ), (-1385513687574815372741853615465231758363924213155841300962496 : ℤ), (1027177741734385181399141411693077346500643446348660292210996 : ℤ)⟩ := by
  rw [show (JPosA).part 1 = dAdd ((JLf5DihA).part 1) ((JLf6DihB).part 1) from rfl, p1_Lf5DihA, p1_Lf6DihB]
  rfl

theorem p2_PosA : (JPosA).part 2 = ⟨(198 : ℤ), (-1419119267711744630089217533882701802946909473303701473927269 : ℤ), (1056088833828851878150909434614253364758564407048757120048855 : ℤ)⟩ := by
  rw [show (JPosA).part 2 = dAdd ((JLf5DihA).part 2) ((JLf6DihB).part 2) from rfl, p2_Lf5DihA, p2_Lf6DihB]
  rfl

def JPos : DCJet := DCJetKit.mul JK2 JPosA
theorem JPos_mem : JetMem JPos fPos D :=
  DCJetKit.mul_mem (JK2_mem) (JPosA_mem)

theorem op_Pos : dMul ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ ⟨(201 : ℤ), (-925630861911283293041087549890518605279408039762222046469242 : ℤ), (1303510218407846659727398999032844926329546828226739606034841 : ℤ)⟩ = ⟨(205 : ℤ), (-958472515681818849424621041223523538363676994463991145579551 : ℤ), (1349759142294103961394669718966828634110007128148620273444042 : ℤ)⟩ := by
  rfl

theorem ev_Pos : (JPos).value = ⟨(205 : ℤ), (-958472515681818849424621041223523538363676994463991145579551 : ℤ), (1349759142294103961394669718966828634110007128148620273444042 : ℤ)⟩ := by
  rw [show (JPos).value = dMul (JK2).value (JPosA).value from rfl, ev_K2, ev_PosA]
  exact op_Pos

theorem p0_Pos : (JPos).part 0 = ⟨(202 : ℤ), (-1566959522029632005633221049516768098386670698018446175009119 : ℤ), (1158063523419754624180704605863498054992611223722692281643495 : ℤ)⟩ := by
  rw [show (JPos).part 0 = dAdd (dMul (JK2).value ((JPosA).part 0)) (dMul (JPosA).value ((JK2).part 0)) from rfl, ev_K2, ev_PosA, p0_K2, p0_PosA]
  rfl

theorem p1_Pos : (JPos).part 1 = ⟨(202 : ℤ), (-1434672118536931707468537755797295085760537610385410872602881 : ℤ), (1063622308508212684763713523641761655614266687045110663032112 : ℤ)⟩ := by
  rw [show (JPos).part 1 = dAdd (dMul (JK2).value ((JPosA).part 1)) (dMul (JPosA).value ((JK2).part 1)) from rfl, ev_K2, ev_PosA, p1_K2, p1_PosA]
  rfl

theorem p2_Pos : (JPos).part 2 = ⟨(202 : ℤ), (-1469470034488308773980238953722581077810542186072397557968920 : ℤ), (1093559174608025311953226188382462325869617637143190543943522 : ℤ)⟩ := by
  rw [show (JPos).part 2 = dAdd (dMul (JK2).value ((JPosA).part 2)) (dMul (JPosA).value ((JK2).part 2)) from rfl, ev_K2, ev_PosA, p2_K2, p2_PosA]
  rfl

def JNeg2 : DCJet := DCJetKit.mul JC008 JDihC
theorem JNeg2_mem : JetMem JNeg2 fNeg2 D :=
  DCJetKit.mul_mem (JC008_mem D) (JDihC_mem)

theorem op_Neg2 : dMul ⟨(206 : ℤ), (822752278660603021077484591278675252491367932816789931674304 : ℤ), (822752278660603021077484591278675252491367932816789931674305 : ℤ)⟩ ⟨(201 : ℤ), (-709494022124609272588572335351235171406713056651246288396128 : ℤ), (1461732507899842465624637272289933830125317106250784804573663 : ℤ)⟩ = ⟨(208 : ℤ), (-726521878655599895130698071399664815520474170010876199317636 : ℤ), (1496814088089438684799628566824892242048324716800803639883432 : ℤ)⟩ := by
  rfl

theorem ev_Neg2 : (JNeg2).value = ⟨(208 : ℤ), (-726521878655599895130698071399664815520474170010876199317636 : ℤ), (1496814088089438684799628566824892242048324716800803639883432 : ℤ)⟩ := by
  rw [show (JNeg2).value = dMul (JC008).value (JDihC).value from rfl, ev_C008, ev_DihC]
  exact op_Neg2

theorem p0_Neg2 : (JNeg2).part 0 = ⟨(205 : ℤ), (-889986527930197203853350958328369212491282262834347245083365 : ℤ), (838908652146687146694627310653157370498426325674441862317220 : ℤ)⟩ := by
  rw [show (JNeg2).part 0 = dAdd (dMul (JC008).value ((JDihC).part 0)) (dMul (JDihC).value ((JC008).part 0)) from rfl, ev_C008, ev_DihC, p0_C008, p0_DihC]
  rfl

theorem p1_Neg2 : (JNeg2).part 1 = ⟨(205 : ℤ), (-1318355926767998157346254933974899896721349600301931789483348 : ℤ), (1032335013112239440444969951440043276308838211943004751464019 : ℤ)⟩ := by
  rw [show (JNeg2).part 1 = dAdd (dMul (JC008).value ((JDihC).part 1)) (dMul (JDihC).value ((JC008).part 1)) from rfl, ev_C008, ev_DihC, p1_C008, p1_DihC]
  rfl

theorem p2_Neg2 : (JNeg2).part 2 = ⟨(205 : ℤ), (-1350770408147077251770005857523269346343305897012930714727539 : ℤ), (1058526082140365159753296209481709790917192078445922046974059 : ℤ)⟩ := by
  rw [show (JNeg2).part 2 = dAdd (dMul (JC008).value ((JDihC).part 2)) (dMul (JDihC).value ((JC008).part 2)) from rfl, ev_C008, ev_DihC, p2_C008, p2_DihC]
  rfl

def JFirstPos : DCJet := DCJetKit.add JFirst JPos
theorem JFirstPos_mem : JetMem JFirstPos fFirstPos D :=
  DCJetKit.add_mem (JFirst_mem) (JPos_mem)

theorem op_FirstPos : dAdd ⟨(203 : ℤ), (71749655407714247971638526003167809604480738375056861867280 : ℤ), (118787907447991386590573456494462910843805561836481214529215 : ℤ)⟩ ⟨(205 : ℤ), (-958472515681818849424621041223523538363676994463991145579551 : ℤ), (1349759142294103961394669718966828634110007128148620273444042 : ℤ)⟩ = ⟨(204 : ℤ), (-335736947025480928769033468605426149972877020481881849055216 : ℤ), (912455386043034753878481772472340138742614687747272565780451 : ℤ)⟩ := by
  rfl

theorem ev_FirstPos : (JFirstPos).value = ⟨(204 : ℤ), (-335736947025480928769033468605426149972877020481881849055216 : ℤ), (912455386043034753878481772472340138742614687747272565780451 : ℤ)⟩ := by
  rw [show (JFirstPos).value = dAdd (JFirst).value (JPos).value from rfl, ev_First, ev_Pos]
  exact op_FirstPos

theorem p0_FirstPos : (JFirstPos).part 0 = ⟨(202 : ℤ), (-1439299255887806076517469008334245242828831942173884960037037 : ℤ), (1316121549056404064541097368717116688467330633579083806798434 : ℤ)⟩ := by
  rw [show (JFirstPos).part 0 = dAdd ((JFirst).part 0) ((JPos).part 0) from rfl, p0_First, p0_Pos]
  rfl

theorem p1_FirstPos : (JFirstPos).part 1 = ⟨(202 : ℤ), (-1269738813743255991226792783818178107954111827125086372564137 : ℤ), (1265790842161239050674012162806635117747251145532143853602978 : ℤ)⟩ := by
  rw [show (JFirstPos).part 1 = dAdd ((JFirst).part 1) ((JPos).part 1) from rfl, p1_First, p1_Pos]
  rfl

theorem p2_FirstPos : (JFirstPos).part 2 = ⟨(202 : ℤ), (-1309399666236917807832371726110329578409816462456461416447980 : ℤ), (1291287674449301665869771626864309910290702358441048595692014 : ℤ)⟩ := by
  rw [show (JFirstPos).part 2 = dAdd ((JFirst).part 2) ((JPos).part 2) from rfl, p2_First, p2_Pos]
  rfl

def JTop : DCJet := DCJetKit.sub JFirstPos JNeg2
theorem JTop_mem : JetMem JTop fTop D :=
  DCJetKit.sub_mem (JFirstPos_mem) (JNeg2_mem)

theorem op_Top : dAdd ⟨(204 : ℤ), (-335736947025480928769033468605426149972877020481881849055216 : ℤ), (912455386043034753878481772472340138742614687747272565780451 : ℤ)⟩ (dNeg ⟨(208 : ℤ), (-726521878655599895130698071399664815520474170010876199317636 : ℤ), (1496814088089438684799628566824892242048324716800803639883432 : ℤ)⟩) = ⟨(204 : ℤ), (-429287827531070846569010254031981915100897315281932076547931 : ℤ), (957863003459009747324150401934819189712644323372952328237804 : ℤ)⟩ := by
  rfl

theorem ev_Top : (JTop).value = ⟨(204 : ℤ), (-429287827531070846569010254031981915100897315281932076547931 : ℤ), (957863003459009747324150401934819189712644323372952328237804 : ℤ)⟩ := by
  rw [show (JTop).value = dAdd (JFirstPos).value (dNeg (JNeg2).value) from rfl, ev_FirstPos, ev_Neg2]
  exact op_Top

theorem p0_Top : (JTop).part 0 = ⟨(202 : ℤ), (-1544162837406141969854297422165889914141135232883190192826690 : ℤ), (1427369865047678715022766238508162840028740916433377212433855 : ℤ)⟩ := by
  rw [show (JTop).part 0 = dAdd ((JFirstPos).part 0) (dNeg ((JNeg2).part 0)) from rfl, p0_FirstPos, p0_Neg2]
  rfl

theorem p1_Top : (JTop).part 1 = ⟨(202 : ℤ), (-1398780690382285921282414027748183517492716603617961966497140 : ℤ), (1430585333007238820342294029553497604837419845569885327288397 : ℤ)⟩ := by
  rw [show (JTop).part 1 = dAdd ((JFirstPos).part 1) (dNeg ((JNeg2).part 1)) from rfl, p1_FirstPos, p1_Neg2]
  rfl

theorem p2_Top : (JTop).part 2 = ⟨(202 : ℤ), (-1441715426504463452801533752295543302274465472262201672319738 : ℤ), (1460133975467686322341022359054718578583615595567664935032957 : ℤ)⟩ := by
  rw [show (JTop).part 2 = dAdd ((JFirstPos).part 2) (dNeg ((JNeg2).part 2)) from rfl, p2_FirstPos, p2_Neg2]
  rfl

end Box


/-! ## 3c. The point coordinate brackets -/

def P4 : DC := ⟨(201 : ℤ), (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) + ((4049483871533651860230706817030176796531686758792705811703733 : ℤ))), (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) + ((4049483871533651860230706817030176796531686758792705811703733 : ℤ)))⟩
theorem P4_mem : P4.mem (c 0) := by
  have h : c0 = ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) + (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ)) * (2 : ℝ) ^ (-(201 : ℤ)) := by
    simp only [c0, s2]
  change ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) + ((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ)) ≤ c0 ∧
    c0 ≤ ((((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) + ((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ))
  rw [h]; constructor <;> norm_num

def P5 : DC := ⟨(201 : ℤ), (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) + ((3734842111502011420851541171028160066896758316960222749146863 : ℤ))), (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) + ((3734842111502011420851541171028160066896758316960222749146863 : ℤ)))⟩
theorem P5_mem : P5.mem (c 1) := by
  have h : c1 = ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) + (((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) : ℝ)) * (2 : ℝ) ^ (-(201 : ℤ)) := by
    simp only [c1, s2]
  change ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) + ((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ)) ≤ c1 ∧
    c1 ≤ ((((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) + ((3734842111502011420851541171028160066896758316960222749146863 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ))
  rw [h]; constructor <;> norm_num

def P6 : DC := ⟨(201 : ℤ), (((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) + ((3786260064126602103902664808873744373940916659619106874140858 : ℤ))), (((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) + ((3786260064126602103902664808873744373940916659619106874140858 : ℤ)))⟩
theorem P6_mem : P6.mem (c 2) := by
  have h : c2 = ((((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) : ℝ) + (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ)) * (2 : ℝ) ^ (-(201 : ℤ)) := by
    simp only [c2, s2]
  change ((((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) + ((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ)) ≤ c2 ∧
    c2 ≤ ((((3697021906849702090774160988178878465989773336804422257896241 : ℤ)) + ((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (-(201 : ℤ))
  rw [h]; constructor <;> norm_num


/-! ## 4. Point pass -/

namespace Pt

def JY4 : DCJet := DCJetKit.coord 0 P4
theorem JY4_mem : JetMem JY4 fY4 Dpt :=
  DCJetKit.coord_mem 0 P4 Dpt (fun x hx => by rw [show x = c from hx]; exact P4_mem)

theorem ev_Y4 : (JY4).value = ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ := by rfl

def JY5 : DCJet := DCJetKit.coord 1 P5
theorem JY5_mem : JetMem JY5 fY5 Dpt :=
  DCJetKit.coord_mem 1 P5 Dpt (fun x hx => by rw [show x = c from hx]; exact P5_mem)

theorem ev_Y5 : (JY5).value = ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ := by rfl

def JY6 : DCJet := DCJetKit.coord 2 P6
theorem JY6_mem : JetMem JY6 fY6 Dpt :=
  DCJetKit.coord_mem 2 P6 Dpt (fun x hx => by rw [show x = c from hx]; exact P6_mem)

theorem ev_Y6 : (JY6).value = ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ := by rfl

def JX4 : DCJet := DCJetKit.mul JY4 JY4
theorem JX4_mem : JetMem JX4 fX4 Dpt :=
  DCJetKit.mul_mem (JY4_mem) (JY4_mem)

theorem op_X4 : dMul ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ = ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ := by
  rfl

theorem ev_X4 : (JX4).value = ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ := by
  rw [show (JX4).value = dMul (JY4).value (JY4).value from rfl, ev_Y4]
  exact op_X4

def JX5 : DCJet := DCJetKit.mul JY5 JY5
theorem JX5_mem : JetMem JX5 fX5 Dpt :=
  DCJetKit.mul_mem (JY5_mem) (JY5_mem)

theorem op_X5 : dMul ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ = ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ := by
  rfl

theorem ev_X5 : (JX5).value = ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ := by
  rw [show (JX5).value = dMul (JY5).value (JY5).value from rfl, ev_Y5]
  exact op_X5

def JX6 : DCJet := DCJetKit.mul JY6 JY6
theorem JX6_mem : JetMem JX6 fX6 Dpt :=
  DCJetKit.mul_mem (JY6_mem) (JY6_mem)

theorem op_X6 : dMul ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ = ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ := by
  rfl

theorem ev_X6 : (JX6).value = ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ := by
  rw [show (JX6).value = dMul (JY6).value (JY6).value from rfl, ev_Y6]
  exact op_X6

def JX4sq : DCJet := DCJetKit.mul JX4 JX4
theorem JX4sq_mem : JetMem JX4sq fX4sq Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX4_mem)

theorem op_X4sq : dMul ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ = ⟨(194 : ℤ), (1012561293625624184990543878740566516508094459825055113984504 : ℤ), (1012561293625624184990543878740566516508094459825055113984507 : ℤ)⟩ := by
  rfl

theorem ev_X4sq : (JX4sq).value = ⟨(194 : ℤ), (1012561293625624184990543878740566516508094459825055113984504 : ℤ), (1012561293625624184990543878740566516508094459825055113984507 : ℤ)⟩ := by
  rw [show (JX4sq).value = dMul (JX4).value (JX4).value from rfl, ev_X4]
  exact op_X4sq

def JX5sq : DCJet := DCJetKit.mul JX5 JX5
theorem JX5sq_mem : JetMem JX5sq fX5sq Dpt :=
  DCJetKit.mul_mem (JX5_mem) (JX5_mem)

theorem op_X5sq : dMul ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(195 : ℤ), (1405351431020510072701801934877111440647095646450265690146951 : ℤ), (1405351431020510072701801934877111440647095646450265690146954 : ℤ)⟩ := by
  rfl

theorem ev_X5sq : (JX5sq).value = ⟨(195 : ℤ), (1405351431020510072701801934877111440647095646450265690146951 : ℤ), (1405351431020510072701801934877111440647095646450265690146954 : ℤ)⟩ := by
  rw [show (JX5sq).value = dMul (JX5).value (JX5).value from rfl, ev_X5]
  exact op_X5sq

def JX6sq : DCJet := DCJetKit.mul JX6 JX6
theorem JX6sq_mem : JetMem JX6sq fX6sq Dpt :=
  DCJetKit.mul_mem (JX6_mem) (JX6_mem)

theorem op_X6sq : dMul ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(195 : ℤ), (1476050036455609296629769890625283569539161475826981030194412 : ℤ), (1476050036455609296629769890625283569539161475826981030194416 : ℤ)⟩ := by
  rfl

theorem ev_X6sq : (JX6sq).value = ⟨(195 : ℤ), (1476050036455609296629769890625283569539161475826981030194412 : ℤ), (1476050036455609296629769890625283569539161475826981030194416 : ℤ)⟩ := by
  rw [show (JX6sq).value = dMul (JX6).value (JX6).value from rfl, ev_X6]
  exact op_X6sq

def JS2a : DCJet := DCJetKit.add JX4sq JX5sq
theorem JS2a_mem : JetMem JS2a fS2a Dpt :=
  DCJetKit.add_mem (JX4sq_mem) (JX5sq_mem)

theorem op_S2a : dAdd ⟨(194 : ℤ), (1012561293625624184990543878740566516508094459825055113984504 : ℤ), (1012561293625624184990543878740566516508094459825055113984507 : ℤ)⟩ ⟨(195 : ℤ), (1405351431020510072701801934877111440647095646450265690146951 : ℤ), (1405351431020510072701801934877111440647095646450265690146954 : ℤ)⟩ = ⟨(193 : ℤ), (857618504567939610670722423089561118415821141525093979528989 : ℤ), (857618504567939610670722423089561118415821141525093979528992 : ℤ)⟩ := by
  rfl

theorem ev_S2a : (JS2a).value = ⟨(193 : ℤ), (857618504567939610670722423089561118415821141525093979528989 : ℤ), (857618504567939610670722423089561118415821141525093979528992 : ℤ)⟩ := by
  rw [show (JS2a).value = dAdd (JX4sq).value (JX5sq).value from rfl, ev_X4sq, ev_X5sq]
  exact op_S2a

def JS2 : DCJet := DCJetKit.add JS2a JX6sq
theorem JS2_mem : JetMem JS2 fS2 Dpt :=
  DCJetKit.add_mem (JS2a_mem) (JX6sq_mem)

theorem op_S2 : dAdd ⟨(193 : ℤ), (857618504567939610670722423089561118415821141525093979528989 : ℤ), (857618504567939610670722423089561118415821141525093979528992 : ℤ)⟩ ⟨(195 : ℤ), (1476050036455609296629769890625283569539161475826981030194412 : ℤ), (1476050036455609296629769890625283569539161475826981030194416 : ℤ)⟩ = ⟨(193 : ℤ), (1226631013681841934828164895745882010800611510481839237077592 : ℤ), (1226631013681841934828164895745882010800611510481839237077596 : ℤ)⟩ := by
  rfl

theorem ev_S2 : (JS2).value = ⟨(193 : ℤ), (1226631013681841934828164895745882010800611510481839237077592 : ℤ), (1226631013681841934828164895745882010800611510481839237077596 : ℤ)⟩ := by
  rw [show (JS2).value = dAdd (JS2a).value (JX6sq).value from rfl, ev_S2a, ev_X6sq]
  exact op_S2

def JX4X5 : DCJet := DCJetKit.mul JX4 JX5
theorem JX4X5_mem : JetMem JX4X5 fX4X5 Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX5_mem)

theorem op_X4X5 : dMul ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(194 : ℤ), (843505916693163994190352864075149517913195060386210544961215 : ℤ), (843505916693163994190352864075149517913195060386210544961217 : ℤ)⟩ := by
  rfl

theorem ev_X4X5 : (JX4X5).value = ⟨(194 : ℤ), (843505916693163994190352864075149517913195060386210544961215 : ℤ), (843505916693163994190352864075149517913195060386210544961217 : ℤ)⟩ := by
  rw [show (JX4X5).value = dMul (JX4).value (JX5).value from rfl, ev_X4, ev_X5]
  exact op_X4X5

def JX4X6 : DCJet := DCJetKit.mul JX4 JX6
theorem JX4X6_mem : JetMem JX4X6 fX4X6 Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX6_mem)

theorem op_X4X6 : dMul ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(194 : ℤ), (864462588655414713766053284498715106696183576974986927829853 : ℤ), (864462588655414713766053284498715106696183576974986927829856 : ℤ)⟩ := by
  rfl

theorem ev_X4X6 : (JX4X6).value = ⟨(194 : ℤ), (864462588655414713766053284498715106696183576974986927829853 : ℤ), (864462588655414713766053284498715106696183576974986927829856 : ℤ)⟩ := by
  rw [show (JX4X6).value = dMul (JX4).value (JX6).value from rfl, ev_X4, ev_X6]
  exact op_X4X6

def JX5X6 : DCJet := DCJetKit.mul JX5 JX6
theorem JX5X6_mem : JetMem JX5X6 fX5X6 Dpt :=
  DCJetKit.mul_mem (JX5_mem) (JX6_mem)

theorem op_X5X6 : dMul ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(195 : ℤ), (1440266999896465928381346386483458509715055043766952185954455 : ℤ), (1440266999896465928381346386483458509715055043766952185954458 : ℤ)⟩ := by
  rfl

theorem ev_X5X6 : (JX5X6).value = ⟨(195 : ℤ), (1440266999896465928381346386483458509715055043766952185954455 : ℤ), (1440266999896465928381346386483458509715055043766952185954458 : ℤ)⟩ := by
  rw [show (JX5X6).value = dMul (JX5).value (JX6).value from rfl, ev_X5, ev_X6]
  exact op_X5X6

def JS1a : DCJet := DCJetKit.add JX4X5 JX4X6
theorem JS1a_mem : JetMem JS1a fS1a Dpt :=
  DCJetKit.add_mem (JX4X5_mem) (JX4X6_mem)

theorem op_S1a : dAdd ⟨(194 : ℤ), (843505916693163994190352864075149517913195060386210544961215 : ℤ), (843505916693163994190352864075149517913195060386210544961217 : ℤ)⟩ ⟨(194 : ℤ), (864462588655414713766053284498715106696183576974986927829853 : ℤ), (864462588655414713766053284498715106696183576974986927829856 : ℤ)⟩ = ⟨(193 : ℤ), (853984252674289353978203074286932312304689318680598736395534 : ℤ), (853984252674289353978203074286932312304689318680598736395537 : ℤ)⟩ := by
  rfl

theorem ev_S1a : (JS1a).value = ⟨(193 : ℤ), (853984252674289353978203074286932312304689318680598736395534 : ℤ), (853984252674289353978203074286932312304689318680598736395537 : ℤ)⟩ := by
  rw [show (JS1a).value = dAdd (JX4X5).value (JX4X6).value from rfl, ev_X4X5, ev_X4X6]
  exact op_S1a

def JS1 : DCJet := DCJetKit.add JS1a JX5X6
theorem JS1_mem : JetMem JS1 fS1 Dpt :=
  DCJetKit.add_mem (JS1a_mem) (JX5X6_mem)

theorem op_S1 : dAdd ⟨(193 : ℤ), (853984252674289353978203074286932312304689318680598736395534 : ℤ), (853984252674289353978203074286932312304689318680598736395537 : ℤ)⟩ ⟨(195 : ℤ), (1440266999896465928381346386483458509715055043766952185954455 : ℤ), (1440266999896465928381346386483458509715055043766952185954458 : ℤ)⟩ = ⟨(193 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ := by
  rfl

theorem ev_S1 : (JS1).value = ⟨(193 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ := by
  rw [show (JS1).value = dAdd (JS1a).value (JX5X6).value from rfl, ev_S1a, ev_X5X6]
  exact op_S1

def JCN2S2 : DCJet := DCJetKit.mul JCN2 JS2
theorem JCN2S2_mem : JetMem JCN2S2 fCN2S2 Dpt :=
  DCJetKit.mul_mem (JCN2_mem Dpt) (JS2_mem)

theorem op_CN2S2 : dMul ⟨(0 : ℤ), (-2 : ℤ), (-2 : ℤ)⟩ ⟨(193 : ℤ), (1226631013681841934828164895745882010800611510481839237077592 : ℤ), (1226631013681841934828164895745882010800611510481839237077596 : ℤ)⟩ = ⟨(192 : ℤ), (-1226631013681841934828164895745882010800611510481839237077596 : ℤ), (-1226631013681841934828164895745882010800611510481839237077592 : ℤ)⟩ := by
  rfl

theorem ev_CN2S2 : (JCN2S2).value = ⟨(192 : ℤ), (-1226631013681841934828164895745882010800611510481839237077596 : ℤ), (-1226631013681841934828164895745882010800611510481839237077592 : ℤ)⟩ := by
  rw [show (JCN2S2).value = dMul (JCN2).value (JS2).value from rfl, ev_CN2, ev_S2]
  exact op_CN2S2

def JC4S1 : DCJet := DCJetKit.mul JC4 JS1
theorem JC4S1_mem : JetMem JC4S1 fC4S1 Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JS1_mem)

theorem op_C4S1 : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(193 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ = ⟨(191 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ := by
  rfl

theorem ev_C4S1 : (JC4S1).value = ⟨(191 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ := by
  rw [show (JC4S1).value = dMul (JC4).value (JS1).value from rfl, ev_C4, ev_S1]
  exact op_C4S1

def JDltA : DCJet := DCJetKit.add JCN2S2 JC4S1
theorem JDltA_mem : JetMem JDltA fDltA Dpt :=
  DCJetKit.add_mem (JCN2S2_mem) (JC4S1_mem)

theorem op_DltA : dAdd ⟨(192 : ℤ), (-1226631013681841934828164895745882010800611510481839237077596 : ℤ), (-1226631013681841934828164895745882010800611510481839237077592 : ℤ)⟩ ⟨(191 : ℤ), (1214051002648405836073539670907796939733453079622336782884147 : ℤ), (1214051002648405836073539670907796939733453079622336782884152 : ℤ)⟩ = ⟨(192 : ℤ), (1201470991614969737318914446069711868666294648762834328690698 : ℤ), (1201470991614969737318914446069711868666294648762834328690712 : ℤ)⟩ := by
  rfl

theorem ev_DltA : (JDltA).value = ⟨(192 : ℤ), (1201470991614969737318914446069711868666294648762834328690698 : ℤ), (1201470991614969737318914446069711868666294648762834328690712 : ℤ)⟩ := by
  rw [show (JDltA).value = dAdd (JCN2S2).value (JC4S1).value from rfl, ev_CN2S2, ev_C4S1]
  exact op_DltA

def JX4X5X6 : DCJet := DCJetKit.mul JX4X5 JX6
theorem JX4X5X6_mem : JetMem JX4X5X6 fX4X5X6 Dpt :=
  DCJetKit.mul_mem (JX4X5_mem) (JX6_mem)

theorem op_X4X5X6 : dMul ⟨(194 : ℤ), (843505916693163994190352864075149517913195060386210544961215 : ℤ), (843505916693163994190352864075149517913195060386210544961217 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(192 : ℤ), (1143283944518095956241556757385292761685541864573942191469300 : ℤ), (1143283944518095956241556757385292761685541864573942191469305 : ℤ)⟩ := by
  rfl

theorem ev_X4X5X6 : (JX4X5X6).value = ⟨(192 : ℤ), (1143283944518095956241556757385292761685541864573942191469300 : ℤ), (1143283944518095956241556757385292761685541864573942191469305 : ℤ)⟩ := by
  rw [show (JX4X5X6).value = dMul (JX4X5).value (JX6).value from rfl, ev_X4X5, ev_X6]
  exact op_X4X5X6

def JDlt : DCJet := DCJetKit.sub JDltA JX4X5X6
theorem JDlt_mem : JetMem JDlt fDlt Dpt :=
  DCJetKit.sub_mem (JDltA_mem) (JX4X5X6_mem)

theorem op_Dlt : dAdd ⟨(192 : ℤ), (1201470991614969737318914446069711868666294648762834328690698 : ℤ), (1201470991614969737318914446069711868666294648762834328690712 : ℤ)⟩ (dNeg ⟨(192 : ℤ), (1143283944518095956241556757385292761685541864573942191469300 : ℤ), (1143283944518095956241556757385292761685541864573942191469305 : ℤ)⟩) = ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ := by
  rfl

theorem ev_Dlt : (JDlt).value = ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ := by
  rw [show (JDlt).value = dAdd (JDltA).value (dNeg (JX4X5X6).value) from rfl, ev_DltA, ev_X4X5X6]
  exact op_Dlt

def JSIY5 : DCJet := DCJetKit.mul JSI JY5
theorem JSIY5_mem : JetMem JSIY5 fSIY5 Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JY5_mem)

theorem op_SIY5 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ = ⟨(198 : ℤ), (1306736691597962201129592839044164214085616870887779184378928 : ℤ), (1306736691597962201931037145670471393677693945779187349564370 : ℤ)⟩ := by
  rfl

theorem ev_SIY5 : (JSIY5).value = ⟨(198 : ℤ), (1306736691597962201129592839044164214085616870887779184378928 : ℤ), (1306736691597962201931037145670471393677693945779187349564370 : ℤ)⟩ := by
  rw [show (JSIY5).value = dMul (JSI).value (JY5).value from rfl, ev_SI, ev_Y5]
  exact op_SIY5

def JSIY5Y4 : DCJet := DCJetKit.mul JSIY5 JY4
theorem JSIY5Y4_mem : JetMem JSIY5Y4 fSIY5Y4 Dpt :=
  DCJetKit.mul_mem (JSIY5_mem) (JY4_mem)

theorem op_SIY5Y4 : dMul ⟨(198 : ℤ), (1306736691597962201129592839044164214085616870887779184378928 : ℤ), (1306736691597962201931037145670471393677693945779187349564370 : ℤ)⟩ ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ = ⟨(196 : ℤ), (823244115706817465338925788658222003966928746606713591894302 : ℤ), (823244115706817465843835701832857643050922375726255019894821 : ℤ)⟩ := by
  rfl

theorem ev_SIY5Y4 : (JSIY5Y4).value = ⟨(196 : ℤ), (823244115706817465338925788658222003966928746606713591894302 : ℤ), (823244115706817465843835701832857643050922375726255019894821 : ℤ)⟩ := by
  rw [show (JSIY5Y4).value = dMul (JSIY5).value (JY4).value from rfl, ev_SIY5, ev_Y4]
  exact op_SIY5Y4

def JY5X4 : DCJet := DCJetKit.mul JY5 JX4
theorem JY5X4_mem : JetMem JY5X4 fY5X4 Dpt :=
  DCJetKit.mul_mem (JY5_mem) (JX4_mem)

theorem op_Y5X4 : dMul ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ = ⟨(196 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ := by
  rfl

theorem ev_Y5X4 : (JY5X4).value = ⟨(196 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ := by
  rw [show (JY5X4).value = dMul (JY5).value (JX4).value from rfl, ev_Y5, ev_X4]
  exact op_Y5X4

def JY5X4CH : DCJet := DCJetKit.mul JY5X4 JCH
theorem JY5X4CH_mem : JetMem JY5X4CH fY5X4CH Dpt :=
  DCJetKit.mul_mem (JY5X4_mem) (JCH_mem Dpt)

theorem op_Y5X4CH : dMul ⟨(196 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ := by
  rfl

theorem ev_Y5X4CH : (JY5X4CH).value = ⟨(197 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ := by
  rw [show (JY5X4CH).value = dMul (JY5X4).value (JCH).value from rfl, ev_Y5X4, ev_CH]
  exact op_Y5X4CH

def JA1 : DCJet := DCJetKit.add JSIY5Y4 JY5X4CH
theorem JA1_mem : JetMem JA1 fA1 Dpt :=
  DCJetKit.add_mem (JSIY5Y4_mem) (JY5X4CH_mem)

theorem op_A1 : dAdd ⟨(196 : ℤ), (823244115706817465338925788658222003966928746606713591894302 : ℤ), (823244115706817465843835701832857643050922375726255019894821 : ℤ)⟩ ⟨(197 : ℤ), (1466946171906478211166900954936041698874650082774193972552738 : ℤ), (1466946171906478211166900954936041698874650082774193972552741 : ℤ)⟩ = ⟨(196 : ℤ), (1556717201660056570922376266126242853404253787993810578170671 : ℤ), (1556717201660056571427286179300878492488247417113352006171192 : ℤ)⟩ := by
  rfl

theorem ev_A1 : (JA1).value = ⟨(196 : ℤ), (1556717201660056570922376266126242853404253787993810578170671 : ℤ), (1556717201660056571427286179300878492488247417113352006171192 : ℤ)⟩ := by
  rw [show (JA1).value = dAdd (JSIY5Y4).value (JY5X4CH).value from rfl, ev_SIY5Y4, ev_Y5X4CH]
  exact op_A1

def JX5X4 : DCJet := DCJetKit.add JX5 JX4
theorem JX5X4_mem : JetMem JX5X4 fX5X4 Dpt :=
  DCJetKit.add_mem (JX5_mem) (JX4_mem)

theorem op_X5X4 : dAdd ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ = ⟨(196 : ℤ), (1169102551220919311075211345977784259179011248741024285733779 : ℤ), (1169102551220919311075211345977784259179011248741024285733780 : ℤ)⟩ := by
  rfl

theorem ev_X5X4 : (JX5X4).value = ⟨(196 : ℤ), (1169102551220919311075211345977784259179011248741024285733779 : ℤ), (1169102551220919311075211345977784259179011248741024285733780 : ℤ)⟩ := by
  rw [show (JX5X4).value = dAdd (JX5).value (JX4).value from rfl, ev_X5, ev_X4]
  exact op_X5X4

def JQA : DCJet := DCJetKit.sub JX5X4 JX6
theorem JQA_mem : JetMem JQA fQA Dpt :=
  DCJetKit.sub_mem (JX5X4_mem) (JX6_mem)

theorem op_QA : dAdd ⟨(196 : ℤ), (1169102551220919311075211345977784259179011248741024285733779 : ℤ), (1169102551220919311075211345977784259179011248741024285733780 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩) = ⟨(197 : ℤ), (1249186976144028071880381223497120345649841616771427726991014 : ℤ), (1249186976144028071880381223497120345649841616771427726991017 : ℤ)⟩ := by
  rfl

theorem ev_QA : (JQA).value = ⟨(197 : ℤ), (1249186976144028071880381223497120345649841616771427726991014 : ℤ), (1249186976144028071880381223497120345649841616771427726991017 : ℤ)⟩ := by
  rw [show (JQA).value = dAdd (JX5X4).value (dNeg (JX6).value) from rfl, ev_X5X4, ev_X6]
  exact op_QA

def JSIQA : DCJet := DCJetKit.mul JSI JQA
theorem JSIQA_mem : JetMem JSIQA fSIQA Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JQA_mem)

theorem op_SIQA : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (1249186976144028071880381223497120345649841616771427726991014 : ℤ), (1249186976144028071880381223497120345649841616771427726991017 : ℤ)⟩ = ⟨(196 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ := by
  rfl

theorem ev_SIQA : (JSIQA).value = ⟨(196 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ := by
  rw [show (JSIQA).value = dMul (JSI).value (JQA).value from rfl, ev_SI, ev_QA]
  exact op_SIQA

def JSIQACH : DCJet := DCJetKit.mul JSIQA JCH
theorem JSIQACH_mem : JetMem JSIQACH fSIQACH Dpt :=
  DCJetKit.mul_mem (JSIQA_mem) (JCH_mem Dpt)

theorem op_SIQACH : dMul ⟨(196 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ := by
  rfl

theorem ev_SIQACH : (JSIQACH).value = ⟨(197 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ := by
  rw [show (JSIQACH).value = dMul (JSIQA).value (JCH).value from rfl, ev_SIQA, ev_CH]
  exact op_SIQACH

def JA2 : DCJet := DCJetKit.add JA1 JSIQACH
theorem JA2_mem : JetMem JA2 fA2 Dpt :=
  DCJetKit.add_mem (JA1_mem) (JSIQACH_mem)

theorem op_A2 : dAdd ⟨(196 : ℤ), (1556717201660056570922376266126242853404253787993810578170671 : ℤ), (1556717201660056571427286179300878492488247417113352006171192 : ℤ)⟩ ⟨(197 : ℤ), (883308581801360219899871298203233555446235209111677018188705 : ℤ), (883308581801360220441619791553614849919822905113483891968224 : ℤ)⟩ = ⟨(195 : ℤ), (999185746280368340436155957613929815563685696274824543632511 : ℤ), (999185746280368340824048037538842958724079434835046976077652 : ℤ)⟩ := by
  rfl

theorem ev_A2 : (JA2).value = ⟨(195 : ℤ), (999185746280368340436155957613929815563685696274824543632511 : ℤ), (999185746280368340824048037538842958724079434835046976077652 : ℤ)⟩ := by
  rw [show (JA2).value = dAdd (JA1).value (JSIQACH).value from rfl, ev_A1, ev_SIQACH]
  exact op_A2

def JY4X5 : DCJet := DCJetKit.mul JY4 JX5
theorem JY4X5_mem : JetMem JY4X5 fY4X5 Dpt :=
  DCJetKit.mul_mem (JY4_mem) (JX5_mem)

theorem op_Y4X5 : dMul ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(196 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ := by
  rfl

theorem ev_Y4X5 : (JY4X5).value = ⟨(196 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ := by
  rw [show (JY4X5).value = dMul (JY4).value (JX5).value from rfl, ev_Y4, ev_X5]
  exact op_Y4X5

def JY4X5CH : DCJet := DCJetKit.mul JY4X5 JCH
theorem JY4X5CH_mem : JetMem JY4X5CH fY4X5CH Dpt :=
  DCJetKit.mul_mem (JY4X5_mem) (JCH_mem Dpt)

theorem op_Y4X5CH : dMul ⟨(196 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ := by
  rfl

theorem ev_Y4X5CH : (JY4X5CH).value = ⟨(197 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ := by
  rw [show (JY4X5CH).value = dMul (JY4X5).value (JCH).value from rfl, ev_Y4X5, ev_CH]
  exact op_Y4X5CH

def JA : DCJet := DCJetKit.add JA2 JY4X5CH
theorem JA_mem : JetMem JA fA Dpt :=
  DCJetKit.add_mem (JA2_mem) (JY4X5CH_mem)

theorem op_A : dAdd ⟨(195 : ℤ), (999185746280368340436155957613929815563685696274824543632511 : ℤ), (999185746280368340824048037538842958724079434835046976077652 : ℤ)⟩ ⟨(197 : ℤ), (1338898280465174956950992715381128620988554676210223534969899 : ℤ), (1338898280465174956950992715381128620988554676210223534969901 : ℤ)⟩ = ⟨(195 : ℤ), (1333910316396662079673904136459211970810824365327380427374985 : ℤ), (1333910316396662080061796216384125113971218103887602859820128 : ℤ)⟩ := by
  rfl

theorem ev_A : (JA).value = ⟨(195 : ℤ), (1333910316396662079673904136459211970810824365327380427374985 : ℤ), (1333910316396662080061796216384125113971218103887602859820128 : ℤ)⟩ := by
  rw [show (JA).value = dAdd (JA2).value (JY4X5CH).value from rfl, ev_A2, ev_Y4X5CH]
  exact op_A

def JSIY6 : DCJet := DCJetKit.mul JSI JY6
theorem JSIY6_mem : JetMem JSIY6 fSIY6 Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JY6_mem)

theorem op_SIY6 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ = ⟨(198 : ℤ), (1322869856802094402672334919767879005939826052122047462821072 : ℤ), (1322869856802094403483673976793290660563661229428226895588993 : ℤ)⟩ := by
  rfl

theorem ev_SIY6 : (JSIY6).value = ⟨(198 : ℤ), (1322869856802094402672334919767879005939826052122047462821072 : ℤ), (1322869856802094403483673976793290660563661229428226895588993 : ℤ)⟩ := by
  rw [show (JSIY6).value = dMul (JSI).value (JY6).value from rfl, ev_SI, ev_Y6]
  exact op_SIY6

def JSIY6Y5 : DCJet := DCJetKit.mul JSIY6 JY5
theorem JSIY6Y5_mem : JetMem JSIY6Y5 fSIY6Y5 Dpt :=
  DCJetKit.mul_mem (JSIY6_mem) (JY5_mem)

theorem op_SIY6Y5 : dMul ⟨(198 : ℤ), (1322869856802094402672334919767879005939826052122047462821072 : ℤ), (1322869856802094403483673976793290660563661229428226895588993 : ℤ)⟩ ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ = ⟨(197 : ℤ), (1521321739811927589703690333381831581857789976291841230444330 : ℤ), (1521321739811927590636743376706201781400263200908615409088112 : ℤ)⟩ := by
  rfl

theorem ev_SIY6Y5 : (JSIY6Y5).value = ⟨(197 : ℤ), (1521321739811927589703690333381831581857789976291841230444330 : ℤ), (1521321739811927590636743376706201781400263200908615409088112 : ℤ)⟩ := by
  rw [show (JSIY6Y5).value = dMul (JSIY6).value (JY5).value from rfl, ev_SIY6, ev_Y5]
  exact op_SIY6Y5

def JY6X5 : DCJet := DCJetKit.mul JY6 JX5
theorem JY6X5_mem : JetMem JY6X5 fY6X5 Dpt :=
  DCJetKit.mul_mem (JY6_mem) (JX5_mem)

theorem op_Y6X5 : dMul ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(196 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ := by
  rfl

theorem ev_Y6X5 : (JY6X5).value = ⟨(196 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ := by
  rw [show (JY6X5).value = dMul (JY6).value (JX5).value from rfl, ev_Y6, ev_X5]
  exact op_Y6X5

def JY6X5CH : DCJet := DCJetKit.mul JY6X5 JCH
theorem JY6X5CH_mem : JetMem JY6X5CH fY6X5CH Dpt :=
  DCJetKit.mul_mem (JY6X5_mem) (JCH_mem Dpt)

theorem op_Y6X5CH : dMul ⟨(196 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ := by
  rfl

theorem ev_Y6X5CH : (JY6X5CH).value = ⟨(197 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ := by
  rw [show (JY6X5CH).value = dMul (JY6X5).value (JCH).value from rfl, ev_Y6X5, ev_CH]
  exact op_Y6X5CH

def JB1 : DCJet := DCJetKit.add JSIY6Y5 JY6X5CH
theorem JB1_mem : JetMem JB1 fB1 Dpt :=
  DCJetKit.add_mem (JSIY6Y5_mem) (JY6X5CH_mem)

theorem op_B1 : dAdd ⟨(197 : ℤ), (1521321739811927589703690333381831581857789976291841230444330 : ℤ), (1521321739811927590636743376706201781400263200908615409088112 : ℤ)⟩ ⟨(197 : ℤ), (1237114862169193499634887576748378329942970874053151302366313 : ℤ), (1237114862169193499634887576748378329942970874053151302366316 : ℤ)⟩ = ⟨(196 : ℤ), (1379218300990560544669288955065104955900380425172496266405321 : ℤ), (1379218300990560545135815476727290055671617037480883355727214 : ℤ)⟩ := by
  rfl

theorem ev_B1 : (JB1).value = ⟨(196 : ℤ), (1379218300990560544669288955065104955900380425172496266405321 : ℤ), (1379218300990560545135815476727290055671617037480883355727214 : ℤ)⟩ := by
  rw [show (JB1).value = dAdd (JSIY6Y5).value (JY6X5CH).value from rfl, ev_SIY6Y5, ev_Y6X5CH]
  exact op_B1

def JX6X5 : DCJet := DCJetKit.add JX6 JX5
theorem JX6X5_mem : JetMem JX6X5 fX6X5 Dpt :=
  DCJetKit.add_mem (JX6_mem) (JX5_mem)

theorem op_X6X5 : dAdd ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(196 : ℤ), (1075817904603274418223895746871838454591048858174271816333988 : ℤ), (1075817904603274418223895746871838454591048858174271816333990 : ℤ)⟩ := by
  rfl

theorem ev_X6X5 : (JX6X5).value = ⟨(196 : ℤ), (1075817904603274418223895746871838454591048858174271816333988 : ℤ), (1075817904603274418223895746871838454591048858174271816333990 : ℤ)⟩ := by
  rw [show (JX6X5).value = dAdd (JX6).value (JX5).value from rfl, ev_X6, ev_X5]
  exact op_X6X5

def JQB : DCJet := DCJetKit.sub JX6X5 JX4
theorem JQB_mem : JetMem JQB fQB Dpt :=
  DCJetKit.sub_mem (JX6X5_mem) (JX4_mem)

theorem op_QB : dAdd ⟨(196 : ℤ), (1075817904603274418223895746871838454591048858174271816333988 : ℤ), (1075817904603274418223895746871838454591048858174271816333990 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩) = ⟨(197 : ℤ), (876048389673448500475118827073337127297992054504417849391851 : ℤ), (876048389673448500475118827073337127297992054504417849391856 : ℤ)⟩ := by
  rfl

theorem ev_QB : (JQB).value = ⟨(197 : ℤ), (876048389673448500475118827073337127297992054504417849391851 : ℤ), (876048389673448500475118827073337127297992054504417849391856 : ℤ)⟩ := by
  rw [show (JQB).value = dAdd (JX6X5).value (dNeg (JX4).value) from rfl, ev_X6X5, ev_X4]
  exact op_QB

def JSIQB : DCJet := DCJetKit.mul JSI JQB
theorem JSIQB_mem : JetMem JSIQB fSIQB Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JQB_mem)

theorem op_SIQB : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (876048389673448500475118827073337127297992054504417849391851 : ℤ), (876048389673448500475118827073337127297992054504417849391856 : ℤ)⟩ = ⟨(197 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ := by
  rfl

theorem ev_SIQB : (JSIQB).value = ⟨(197 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ := by
  rw [show (JSIQB).value = dMul (JSI).value (JQB).value from rfl, ev_SI, ev_QB]
  exact op_SIQB

def JSIQBCH : DCJet := DCJetKit.mul JSIQB JCH
theorem JSIQBCH_mem : JetMem JSIQBCH fSIQBCH Dpt :=
  DCJetKit.mul_mem (JSIQB_mem) (JCH_mem Dpt)

theorem op_SIQBCH : dMul ⟨(197 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(198 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ := by
  rfl

theorem ev_SIQBCH : (JSIQBCH).value = ⟨(198 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ := by
  rw [show (JSIQBCH).value = dMul (JSIQB).value (JCH).value from rfl, ev_SIQB, ev_CH]
  exact op_SIQBCH

def JB2 : DCJet := DCJetKit.add JB1 JSIQBCH
theorem JB2_mem : JetMem JB2 fB2 Dpt :=
  DCJetKit.add_mem (JB1_mem) (JSIQBCH_mem)

theorem op_B2 : dAdd ⟨(196 : ℤ), (1379218300990560544669288955065104955900380425172496266405321 : ℤ), (1379218300990560545135815476727290055671617037480883355727214 : ℤ)⟩ ⟨(198 : ℤ), (1238919513971300936965204345935709893220376892359875591033633 : ℤ), (1238919513971300937725055199764814383249828842378271692085136 : ℤ)⟩ = ⟨(195 : ℤ), (844474089741692889455295020774516214602737324131232582081864 : ℤ), (844474089741692889783539638334246825742037124037725639374249 : ℤ)⟩ := by
  rfl

theorem ev_B2 : (JB2).value = ⟨(195 : ℤ), (844474089741692889455295020774516214602737324131232582081864 : ℤ), (844474089741692889783539638334246825742037124037725639374249 : ℤ)⟩ := by
  rw [show (JB2).value = dAdd (JB1).value (JSIQBCH).value from rfl, ev_B1, ev_SIQBCH]
  exact op_B2

def JY5X6 : DCJet := DCJetKit.mul JY5 JX6
theorem JY5X6_mem : JetMem JY5X6 fY5X6 Dpt :=
  DCJetKit.mul_mem (JY5_mem) (JX6_mem)

theorem op_Y5X6 : dMul ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(196 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ := by
  rfl

theorem ev_Y5X6 : (JY5X6).value = ⟨(196 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ := by
  rw [show (JY5X6).value = dMul (JY5).value (JX6).value from rfl, ev_Y5, ev_X6]
  exact op_Y5X6

def JY5X6CH : DCJet := DCJetKit.mul JY5X6 JCH
theorem JY5X6CH_mem : JetMem JY5X6CH fY5X6CH Dpt :=
  DCJetKit.mul_mem (JY5X6_mem) (JCH_mem Dpt)

theorem op_Y5X6CH : dMul ⟨(196 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ := by
  rfl

theorem ev_Y5X6CH : (JY5X6CH).value = ⟨(197 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ := by
  rw [show (JY5X6CH).value = dMul (JY5X6).value (JCH).value from rfl, ev_Y5X6, ev_CH]
  exact op_Y5X6CH

def JB : DCJet := DCJetKit.add JB2 JY5X6CH
theorem JB_mem : JetMem JB fB Dpt :=
  DCJetKit.add_mem (JB2_mem) (JY5X6CH_mem)

theorem op_B : dAdd ⟨(195 : ℤ), (844474089741692889455295020774516214602737324131232582081864 : ℤ), (844474089741692889783539638334246825742037124037725639374249 : ℤ)⟩ ⟨(197 : ℤ), (1252388465930526775994288741366903741460037085722923797615890 : ℤ), (1252388465930526775994288741366903741460037085722923797615892 : ℤ)⟩ = ⟨(195 : ℤ), (1157571206224324583453867206116242149967746595561963531485836 : ℤ), (1157571206224324583782111823675972761107046395468456588778222 : ℤ)⟩ := by
  rfl

theorem ev_B : (JB).value = ⟨(195 : ℤ), (1157571206224324583453867206116242149967746595561963531485836 : ℤ), (1157571206224324583782111823675972761107046395468456588778222 : ℤ)⟩ := by
  rw [show (JB).value = dAdd (JB2).value (JY5X6CH).value from rfl, ev_B2, ev_Y5X6CH]
  exact op_B

def JSIY4 : DCJet := DCJetKit.mul JSI JY4
theorem JSIY4_mem : JetMem JSIY4 fSIY4 Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JY4_mem)

theorem op_SIY4 : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ = ⟨(198 : ℤ), (1431708752933323510956743457238615483401683464961832547267469 : ℤ), (1431708752933323511834835299430866795803190629194023326930744 : ℤ)⟩ := by
  rfl

theorem ev_SIY4 : (JSIY4).value = ⟨(198 : ℤ), (1431708752933323510956743457238615483401683464961832547267469 : ℤ), (1431708752933323511834835299430866795803190629194023326930744 : ℤ)⟩ := by
  rw [show (JSIY4).value = dMul (JSI).value (JY4).value from rfl, ev_SI, ev_Y4]
  exact op_SIY4

def JSIY4Y6 : DCJet := DCJetKit.mul JSIY4 JY6
theorem JSIY4Y6_mem : JetMem JSIY4Y6 fSIY4Y6 Dpt :=
  DCJetKit.mul_mem (JSIY4_mem) (JY6_mem)

theorem op_SIY4Y6 : dMul ⟨(198 : ℤ), (1431708752933323510956743457238615483401683464961832547267469 : ℤ), (1431708752933323511834835299430866795803190629194023326930744 : ℤ)⟩ ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ = ⟨(196 : ℤ), (833408009785422002711822445780442893060047022299245267795445 : ℤ), (833408009785422003222966051706515118306677938532429930784653 : ℤ)⟩ := by
  rfl

theorem ev_SIY4Y6 : (JSIY4Y6).value = ⟨(196 : ℤ), (833408009785422002711822445780442893060047022299245267795445 : ℤ), (833408009785422003222966051706515118306677938532429930784653 : ℤ)⟩ := by
  rw [show (JSIY4Y6).value = dMul (JSIY4).value (JY6).value from rfl, ev_SIY4, ev_Y6]
  exact op_SIY4Y6

def JY4X6 : DCJet := DCJetKit.mul JY4 JX6
theorem JY4X6_mem : JetMem JY4X6 fY4X6 Dpt :=
  DCJetKit.mul_mem (JY4_mem) (JX6_mem)

theorem op_Y4X6 : dMul ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(196 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ := by
  rfl

theorem ev_Y4X6 : (JY4X6).value = ⟨(196 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ := by
  rw [show (JY4X6).value = dMul (JY4).value (JX6).value from rfl, ev_Y4, ev_X6]
  exact op_Y4X6

def JY4X6CH : DCJet := DCJetKit.mul JY4X6 JCH
theorem JY4X6CH_mem : JetMem JY4X6CH fY4X6CH Dpt :=
  DCJetKit.mul_mem (JY4X6_mem) (JCH_mem Dpt)

theorem op_Y4X6CH : dMul ⟨(196 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ := by
  rfl

theorem ev_Y4X6CH : (JY4X6CH).value = ⟨(197 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ := by
  rw [show (JY4X6CH).value = dMul (JY4X6).value (JCH).value from rfl, ev_Y4X6, ev_CH]
  exact op_Y4X6CH

def JC1 : DCJet := DCJetKit.add JSIY4Y6 JY4X6CH
theorem JC1_mem : JetMem JC1 fC1 Dpt :=
  DCJetKit.add_mem (JSIY4Y6_mem) (JY4X6CH_mem)

theorem op_C1 : dAdd ⟨(196 : ℤ), (833408009785422002711822445780442893060047022299245267795445 : ℤ), (833408009785422003222966051706515118306677938532429930784653 : ℤ)⟩ ⟨(197 : ℤ), (1372162839135410102040009673871042056740333653746633759158763 : ℤ), (1372162839135410102040009673871042056740333653746633759158765 : ℤ)⟩ = ⟨(196 : ℤ), (1519489429353127053731827282715963921430213849172562147374826 : ℤ), (1519489429353127054242970888642036146676844765405746810364036 : ℤ)⟩ := by
  rfl

theorem ev_C1 : (JC1).value = ⟨(196 : ℤ), (1519489429353127053731827282715963921430213849172562147374826 : ℤ), (1519489429353127054242970888642036146676844765405746810364036 : ℤ)⟩ := by
  rw [show (JC1).value = dAdd (JSIY4Y6).value (JY4X6CH).value from rfl, ev_SIY4Y6, ev_Y4X6CH]
  exact op_C1

def JX4X6add : DCJet := DCJetKit.add JX4 JX6
theorem JX4X6add_mem : JetMem JX4X6add fX4X6add Dpt :=
  DCJetKit.add_mem (JX4_mem) (JX6_mem)

theorem op_X4X6add : dAdd ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(196 : ℤ), (1182302772915455443121357067564393977296143271277373313876333 : ℤ), (1182302772915455443121357067564393977296143271277373313876335 : ℤ)⟩ := by
  rfl

theorem ev_X4X6add : (JX4X6add).value = ⟨(196 : ℤ), (1182302772915455443121357067564393977296143271277373313876333 : ℤ), (1182302772915455443121357067564393977296143271277373313876335 : ℤ)⟩ := by
  rw [show (JX4X6add).value = dAdd (JX4).value (JX6).value from rfl, ev_X4, ev_X6]
  exact op_X4X6add

def JQC : DCJet := DCJetKit.sub JX4X6add JX5
theorem JQC_mem : JetMem JQC fQC Dpt :=
  DCJetKit.sub_mem (JX4X6add_mem) (JX5_mem)

theorem op_QC : dAdd ⟨(196 : ℤ), (1182302772915455443121357067564393977296143271277373313876333 : ℤ), (1182302772915455443121357067564393977296143271277373313876335 : ℤ)⟩ (dNeg ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩) = ⟨(197 : ℤ), (1301987862922172600064964109843559218118369706916823839561231 : ℤ), (1301987862922172600064964109843559218118369706916823839561236 : ℤ)⟩ := by
  rfl

theorem ev_QC : (JQC).value = ⟨(197 : ℤ), (1301987862922172600064964109843559218118369706916823839561231 : ℤ), (1301987862922172600064964109843559218118369706916823839561236 : ℤ)⟩ := by
  rw [show (JQC).value = dAdd (JX4X6add).value (dNeg (JX5).value) from rfl, ev_X4X6add, ev_X5]
  exact op_QC

def JSIQC : DCJet := DCJetKit.mul JSI JQC
theorem JSIQC_mem : JetMem JSIQC fSIQC Dpt :=
  DCJetKit.mul_mem (JSI_mem Dpt) (JQC_mem)

theorem op_SIQC : dMul ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩ ⟨(197 : ℤ), (1301987862922172600064964109843559218118369706916823839561231 : ℤ), (1301987862922172600064964109843559218118369706916823839561236 : ℤ)⟩ = ⟨(196 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ := by
  rfl

theorem ev_SIQC : (JSIQC).value = ⟨(196 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ := by
  rw [show (JSIQC).value = dMul (JSI).value (JQC).value from rfl, ev_SI, ev_QC]
  exact op_SIQC

def JSIQCCH : DCJet := DCJetKit.mul JSIQC JCH
theorem JSIQCCH_mem : JetMem JSIQCCH fSIQCCH Dpt :=
  DCJetKit.mul_mem (JSIQC_mem) (JCH_mem Dpt)

theorem op_SIQCCH : dMul ⟨(196 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ := by
  rfl

theorem ev_SIQCCH : (JSIQCCH).value = ⟨(197 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ := by
  rw [show (JSIQCCH).value = dMul (JSIQC).value (JCH).value from rfl, ev_SIQC, ev_CH]
  exact op_SIQCCH

def JC2b : DCJet := DCJetKit.add JC1 JSIQCCH
theorem JC2b_mem : JetMem JC2b fC2b Dpt :=
  DCJetKit.add_mem (JC1_mem) (JSIQCCH_mem)

theorem op_C2b : dAdd ⟨(196 : ℤ), (1519489429353127053731827282715963921430213849172562147374826 : ℤ), (1519489429353127054242970888642036146676844765405746810364036 : ℤ)⟩ ⟨(197 : ℤ), (920644446894849333079417652394855358443192514526314086322206 : ℤ), (920644446894849333644064880206846830611962066333002952543948 : ℤ)⟩ = ⟨(195 : ℤ), (989905826400275860135768054456695800325905053217859595267964 : ℤ), (989905826400275860532501664372729780991412899286124143318005 : ℤ)⟩ := by
  rfl

theorem ev_C2b : (JC2b).value = ⟨(195 : ℤ), (989905826400275860135768054456695800325905053217859595267964 : ℤ), (989905826400275860532501664372729780991412899286124143318005 : ℤ)⟩ := by
  rw [show (JC2b).value = dAdd (JC1).value (JSIQCCH).value from rfl, ev_C1, ev_SIQCCH]
  exact op_C2b

def JY6X4 : DCJet := DCJetKit.mul JY6 JX4
theorem JY6X4_mem : JetMem JY6X4 fY6X4 Dpt :=
  DCJetKit.mul_mem (JY6_mem) (JX4_mem)

theorem op_Y6X4 : dMul ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ = ⟨(196 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ := by
  rfl

theorem ev_Y6X4 : (JY6X4).value = ⟨(196 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ := by
  rw [show (JY6X4).value = dMul (JY6).value (JX4).value from rfl, ev_Y6, ev_X4]
  exact op_Y6X4

def JY6X4CH : DCJet := DCJetKit.mul JY6X4 JCH
theorem JY6X4CH_mem : JetMem JY6X4CH fY6X4CH Dpt :=
  DCJetKit.mul_mem (JY6X4_mem) (JCH_mem Dpt)

theorem op_Y6X4CH : dMul ⟨(196 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(197 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ := by
  rfl

theorem ev_Y6X4CH : (JY6X4CH).value = ⟨(197 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ := by
  rw [show (JY6X4CH).value = dMul (JY6X4).value (JCH).value from rfl, ev_Y6X4, ev_CH]
  exact op_Y6X4CH

def JC : DCJet := DCJetKit.add JC2b JY6X4CH
theorem JC_mem : JetMem JC fC Dpt :=
  DCJetKit.add_mem (JC2b_mem) (JY6X4CH_mem)

theorem op_C : dAdd ⟨(195 : ℤ), (989905826400275860135768054456695800325905053217859595267964 : ℤ), (989905826400275860532501664372729780991412899286124143318005 : ℤ)⟩ ⟨(197 : ℤ), (1485057307140612962248187228528887346228779274534253093203848 : ℤ), (1485057307140612962248187228528887346228779274534253093203850 : ℤ)⟩ = ⟨(195 : ℤ), (1361170153185429100697814861588917636883099871851422868568926 : ℤ), (1361170153185429101094548471504951617548607717919687416618968 : ℤ)⟩ := by
  rfl

theorem ev_C : (JC).value = ⟨(195 : ℤ), (1361170153185429100697814861588917636883099871851422868568926 : ℤ), (1361170153185429101094548471504951617548607717919687416618968 : ℤ)⟩ := by
  rw [show (JC).value = dAdd (JC2b).value (JY6X4CH).value from rfl, ev_C2b, ev_Y6X4CH]
  exact op_C

def JD4A : DCJet := DCJetKit.mul JX5 JQC
theorem JD4A_mem : JetMem JD4A fD4A Dpt :=
  DCJetKit.mul_mem (JX5_mem) (JQC_mem)

theorem op_D4A : dMul ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ ⟨(197 : ℤ), (1301987862922172600064964109843559218118369706916823839561231 : ℤ), (1301987862922172600064964109843559218118369706916823839561236 : ℤ)⟩ = ⟨(194 : ℤ), (860963701131141922030125089878323052447174759044553792864966 : ℤ), (860963701131141922030125089878323052447174759044553792864971 : ℤ)⟩ := by
  rfl

theorem ev_D4A : (JD4A).value = ⟨(194 : ℤ), (860963701131141922030125089878323052447174759044553792864966 : ℤ), (860963701131141922030125089878323052447174759044553792864971 : ℤ)⟩ := by
  rw [show (JD4A).value = dMul (JX5).value (JQC).value from rfl, ev_X5, ev_QC]
  exact op_D4A

def JD4B : DCJet := DCJetKit.mul JX6 JQA
theorem JD4B_mem : JetMem JD4B fD4B Dpt :=
  DCJetKit.mul_mem (JX6_mem) (JQA_mem)

theorem op_D4B : dMul ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ ⟨(197 : ℤ), (1249186976144028071880381223497120345649841616771427726991014 : ℤ), (1249186976144028071880381223497120345649841616771427726991017 : ℤ)⟩ = ⟨(194 : ℤ), (846571070375843029641841532427802576784130360944972505709874 : ℤ), (846571070375843029641841532427802576784130360944972505709878 : ℤ)⟩ := by
  rfl

theorem ev_D4B : (JD4B).value = ⟨(194 : ℤ), (846571070375843029641841532427802576784130360944972505709874 : ℤ), (846571070375843029641841532427802576784130360944972505709878 : ℤ)⟩ := by
  rw [show (JD4B).value = dMul (JX6).value (JQA).value from rfl, ev_X6, ev_QA]
  exact op_D4B

def JD4C : DCJet := DCJetKit.mul JX4 JQB
theorem JD4C_mem : JetMem JD4C fD4C Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JQB_mem)

theorem op_D4C : dMul ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(197 : ℤ), (876048389673448500475118827073337127297992054504417849391851 : ℤ), (876048389673448500475118827073337127297992054504417849391856 : ℤ)⟩ = ⟨(195 : ℤ), (1390814423445909045931724539666596216202568355072284717613125 : ℤ), (1390814423445909045931724539666596216202568355072284717613135 : ℤ)⟩ := by
  rfl

theorem ev_D4C : (JD4C).value = ⟨(195 : ℤ), (1390814423445909045931724539666596216202568355072284717613125 : ℤ), (1390814423445909045931724539666596216202568355072284717613135 : ℤ)⟩ := by
  rw [show (JD4C).value = dMul (JX4).value (JQB).value from rfl, ev_X4, ev_QB]
  exact op_D4C

def JKA : DCJet := DCJetKit.mul JC4 JX5
theorem JKA_mem : JetMem JKA fKA Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JX5_mem)

theorem op_KA : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ = ⟨(195 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ := by
  rfl

theorem ev_KA : (JKA).value = ⟨(195 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ := by
  rw [show (JKA).value = dMul (JC4).value (JX5).value from rfl, ev_C4, ev_X5]
  exact op_KA

def JKB : DCJet := DCJetKit.mul JC4 JX6
theorem JKB_mem : JetMem JKB fKB Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JX6_mem)

theorem op_KB : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ = ⟨(195 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ := by
  rfl

theorem ev_KB : (JKB).value = ⟨(195 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ := by
  rw [show (JKB).value = dMul (JC4).value (JX6).value from rfl, ev_C4, ev_X6]
  exact op_KB

def JKC : DCJet := DCJetKit.mul JC4 JX4
theorem JKC_mem : JetMem JKC fKC Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JX4_mem)

theorem op_KC : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(197 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ = ⟨(195 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ := by
  rfl

theorem ev_KC : (JKC).value = ⟨(195 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ := by
  rw [show (JKC).value = dMul (JC4).value (JX4).value from rfl, ev_C4, ev_X4]
  exact op_KC

def JNA : DCJet := DCJetKit.mul JC2 JY5
theorem JNA_mem : JetMem JNA fNA Dpt :=
  DCJetKit.mul_mem (JC2_mem Dpt) (JY5_mem)

theorem op_NA : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ = ⟨(197 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩ := by
  rfl

theorem ev_NA : (JNA).value = ⟨(197 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩ := by
  rw [show (JNA).value = dMul (JC2).value (JY5).value from rfl, ev_C2, ev_Y5]
  exact op_NA

def JNB : DCJet := DCJetKit.mul JC2 JY6
theorem JNB_mem : JetMem JNB fNB Dpt :=
  DCJetKit.mul_mem (JC2_mem Dpt) (JY6_mem)

theorem op_NB : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ = ⟨(197 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩ := by
  rfl

theorem ev_NB : (JNB).value = ⟨(197 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩ := by
  rw [show (JNB).value = dMul (JC2).value (JY6).value from rfl, ev_C2, ev_Y6]
  exact op_NB

def JNC : DCJet := DCJetKit.mul JC2 JY4
theorem JNC_mem : JetMem JNC fNC Dpt :=
  DCJetKit.mul_mem (JC2_mem Dpt) (JY4_mem)

theorem op_NC : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ = ⟨(197 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩ := by
  rfl

theorem ev_NC : (JNC).value = ⟨(197 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩ := by
  rw [show (JNC).value = dMul (JC2).value (JY4).value from rfl, ev_C2, ev_Y4]
  exact op_NC

def JY4CH : DCJet := DCJetKit.mul JY4 JCH
theorem JY4CH_mem : JetMem JY4CH fY4CH Dpt :=
  DCJetKit.mul_mem (JY4_mem) (JCH_mem Dpt)

theorem op_Y4CH : dMul ⟨(201 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ), (8098967743066307354596451289729906554887638303125343756663200 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩ := by
  rfl

theorem ev_Y4CH : (JY4CH).value = ⟨(199 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩ := by
  rw [show (JY4CH).value = dMul (JY4).value (JCH).value from rfl, ev_Y4, ev_CH]
  exact op_Y4CH

def JY5CH : DCJet := DCJetKit.mul JY5 JCH
theorem JY5CH_mem : JetMem JY5CH fY5CH Dpt :=
  DCJetKit.mul_mem (JY5_mem) (JCH_mem Dpt)

theorem op_Y5CH : dMul ⟨(201 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ), (7392019006833546346959095053202110599522038872749889657550835 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩ := by
  rfl

theorem ev_Y5CH : (JY5CH).value = ⟨(199 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩ := by
  rw [show (JY5CH).value = dMul (JY5).value (JCH).value from rfl, ev_Y5, ev_CH]
  exact op_Y5CH

def JY6CH : DCJet := DCJetKit.mul JY6 JCH
theorem JY6CH_mem : JetMem JY6CH fY6CH Dpt :=
  DCJetKit.mul_mem (JY6_mem) (JCH_mem Dpt)

theorem op_Y6CH : dMul ⟨(201 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ), (7483281970976304194676825797052622839930689996423529132037099 : ℤ)⟩ ⟨(200 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ), (803469022129495137770981046170581301261101496891396417650688 : ℤ)⟩ = ⟨(199 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩ := by
  rfl

theorem ev_Y6CH : (JY6CH).value = ⟨(199 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩ := by
  rw [show (JY6CH).value = dMul (JY6).value (JCH).value from rfl, ev_Y6, ev_CH]
  exact op_Y6CH

def JCH0m4 : DCJet := DCJetKit.sub JCH0 JY4CH
theorem JCH0m4_mem : JetMem JCH0m4 fCH0m4 Dpt :=
  DCJetKit.sub_mem (JCH0_mem Dpt) (JY4CH_mem)

theorem op_CH0m4 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩) = ⟨(199 : ℤ), (-124545733120293041305879771966901807508483343034 : ℤ), (-124545733120293041305879771966901807508483343032 : ℤ)⟩ := by
  rfl

theorem ev_CH0m4 : (JCH0m4).value = ⟨(199 : ℤ), (-124545733120293041305879771966901807508483343034 : ℤ), (-124545733120293041305879771966901807508483343032 : ℤ)⟩ := by
  rw [show (JCH0m4).value = dAdd (JCH0).value (dNeg (JY4CH).value) from rfl, ev_CH0, ev_Y4CH]
  exact op_CH0m4

def JCH0m5 : DCJet := DCJetKit.sub JCH0 JY5CH
theorem JCH0m5_mem : JetMem JCH0m5 fCH0m5 Dpt :=
  DCJetKit.sub_mem (JCH0_mem Dpt) (JY5CH_mem)

theorem op_CH0m5 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩) = ⟨(199 : ℤ), (88368592028970580221549236524668614648733026989423279046011 : ℤ), (88368592028970580221549236524668614648733026989423279046014 : ℤ)⟩ := by
  rfl

theorem ev_CH0m5 : (JCH0m5).value = ⟨(199 : ℤ), (88368592028970580221549236524668614648733026989423279046011 : ℤ), (88368592028970580221549236524668614648733026989423279046014 : ℤ)⟩ := by
  rw [show (JCH0m5).value = dAdd (JCH0).value (dNeg (JY5CH).value) from rfl, ev_CH0, ev_Y5CH]
  exact op_CH0m5

def JCH0m6 : DCJet := DCJetKit.sub JCH0 JY6CH
theorem JCH0m6_mem : JetMem JCH0m6 fCH0m6 Dpt :=
  DCJetKit.sub_mem (JCH0_mem Dpt) (JY6CH_mem)

theorem op_CH0m6 : dAdd ⟨(199 : ℤ), (1012370967883163873591436118174932439588987886083159486239866 : ℤ), (1012370967883163873591436118174932439588987886083159486239868 : ℤ)⟩ (dNeg ⟨(199 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩) = ⟨(199 : ℤ), (76960721511125849256832893543354584597651636530218344735228 : ℤ), (76960721511125849256832893543354584597651636530218344735231 : ℤ)⟩ := by
  rfl

theorem ev_CH0m6 : (JCH0m6).value = ⟨(199 : ℤ), (76960721511125849256832893543354584597651636530218344735228 : ℤ), (76960721511125849256832893543354584597651636530218344735231 : ℤ)⟩ := by
  rw [show (JCH0m6).value = dAdd (JCH0).value (dNeg (JY6CH).value) from rfl, ev_CH0, ev_Y6CH]
  exact op_CH0m6

def JLf4 : DCJet := DCJetKit.mul JCH0m4 JCH0i
theorem JLf4_mem : JetMem JLf4 fLf4 Dpt :=
  DCJetKit.mul_mem (JCH0m4_mem) (JCH0i_mem Dpt)

theorem op_Lf4 : dMul ⟨(199 : ℤ), (-124545733120293041305879771966901807508483343034 : ℤ), (-124545733120293041305879771966901807508483343032 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(240 : ℤ), (-1053380628889605211264257483039076150532377995602273311633724 : ℤ), (-1053380628889605211264257483039076150532377995585357748129476 : ℤ)⟩ := by
  rfl

theorem ev_Lf4 : (JLf4).value = ⟨(240 : ℤ), (-1053380628889605211264257483039076150532377995602273311633724 : ℤ), (-1053380628889605211264257483039076150532377995585357748129476 : ℤ)⟩ := by
  rw [show (JLf4).value = dMul (JCH0m4).value (JCH0i).value from rfl, ev_CH0m4, ev_CH0i]
  exact op_Lf4

def JLf5 : DCJet := DCJetKit.mul JCH0m5 JCH0i
theorem JLf5_mem : JetMem JLf5 fLf5 Dpt :=
  DCJetKit.mul_mem (JCH0m5_mem) (JCH0i_mem Dpt)

theorem op_Lf5 : dMul ⟨(199 : ℤ), (88368592028970580221549236524668614648733026989423279046011 : ℤ), (88368592028970580221549236524668614648733026989423279046014 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(201 : ℤ), (1359516800445701234177680561917978686903585030606511985323245 : ℤ), (1359516800445701234177680561917978686903585030606511985323294 : ℤ)⟩ := by
  rfl

theorem ev_Lf5 : (JLf5).value = ⟨(201 : ℤ), (1359516800445701234177680561917978686903585030606511985323245 : ℤ), (1359516800445701234177680561917978686903585030606511985323294 : ℤ)⟩ := by
  rw [show (JLf5).value = dMul (JCH0m5).value (JCH0i).value from rfl, ev_CH0m5, ev_CH0i]
  exact op_Lf5

def JLf6 : DCJet := DCJetKit.mul JCH0m6 JCH0i
theorem JLf6_mem : JetMem JLf6 fLf6 Dpt :=
  DCJetKit.mul_mem (JCH0m6_mem) (JCH0i_mem Dpt)

theorem op_Lf6 : dMul ⟨(199 : ℤ), (76960721511125849256832893543354584597651636530218344735228 : ℤ), (76960721511125849256832893543354584597651636530218344735231 : ℤ)⟩ ⟨(198 : ℤ), (1545132734864413726482655858020348656271349032483454649328245 : ℤ), (1545132734864413726482655858020348656271349032483454649328247 : ℤ)⟩ = ⟨(201 : ℤ), (1184011100171166911643582977590070532271563638926436072849660 : ℤ), (1184011100171166911643582977590070532271563638926436072849709 : ℤ)⟩ := by
  rfl

theorem ev_Lf6 : (JLf6).value = ⟨(201 : ℤ), (1184011100171166911643582977590070532271563638926436072849660 : ℤ), (1184011100171166911643582977590070532271563638926436072849709 : ℤ)⟩ := by
  rw [show (JLf6).value = dMul (JCH0m6).value (JCH0i).value from rfl, ev_CH0m6, ev_CH0i]
  exact op_Lf6

def JINVPI : DCJet := DCJetKit.inv JPI
theorem JINVPI_mem : JetMem JINVPI fINVPI Dpt :=
  DCJetKit.inv_mem (JPI_mem Dpt) (by rw [ev_PI]; decide)

theorem op_INVPI : dInv ⟨(40 : ℤ), (3454217652357 : ℤ), (3454217652358 : ℤ)⟩ = ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ := by
  rfl

theorem ev_INVPI : (JINVPI).value = ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ := by
  rw [show (JINVPI).value = dInv (JPI).value from rfl, ev_PI]
  exact op_INVPI

def JC2MM1 : DCJet := DCJetKit.mul JC2 JMM1
theorem JC2MM1_mem : JetMem JC2MM1 fC2MM1 Dpt :=
  DCJetKit.mul_mem (JC2_mem Dpt) (JMM1_mem Dpt)

theorem op_C2MM1 : dMul ⟨(0 : ℤ), (2 : ℤ), (2 : ℤ)⟩ ⟨(200 : ℤ), (1626351141384074285262729427986317719690753223710083998986084 : ℤ), (1626351302077878711161756982182526953807013475930383377265369 : ℤ)⟩ = ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ := by
  rfl

theorem ev_C2MM1 : (JC2MM1).value = ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ := by
  rw [show (JC2MM1).value = dMul (JC2).value (JMM1).value from rfl, ev_C2, ev_MM1]
  exact op_C2MM1

def JK1 : DCJet := DCJetKit.mul JC2MM1 JINVPI
theorem JK1_mem : JetMem JK1 fK1 Dpt :=
  DCJetKit.mul_mem (JC2MM1_mem) (JINVPI_mem)

theorem op_K1 : dMul ⟨(198 : ℤ), (813175570692037142631364713993158859845376611855041999493042 : ℤ), (813175651038939355580878491091263476903506737965191688632685 : ℤ)⟩ ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ = ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ := by
  rfl

theorem ev_K1 : (JK1).value = ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ := by
  rw [show (JK1).value = dMul (JC2MM1).value (JINVPI).value from rfl, ev_C2MM1, ev_INVPI]
  exact op_K1

def JC8MM2 : DCJet := DCJetKit.mul JC8 JMM2
theorem JC8MM2_mem : JetMem JC8MM2 fC8MM2 Dpt :=
  DCJetKit.mul_mem (JC8_mem Dpt) (JMM2_mem Dpt)

theorem op_C8MM2 : dMul ⟨(0 : ℤ), (8 : ℤ), (8 : ℤ)⟩ ⟨(200 : ℤ), (40839526925820108357761195595804476961800527985492788512766 : ℤ), (40839542995200550947663951015425400373426553207522726340696 : ℤ)⟩ = ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ := by
  rfl

theorem ev_C8MM2 : (JC8MM2).value = ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ := by
  rw [show (JC8MM2).value = dMul (JC8).value (JMM2).value from rfl, ev_C8, ev_MM2]
  exact op_C8MM2

def JK2 : DCJet := DCJetKit.mul JC8MM2 JINVPI
theorem JK2_mem : JetMem JK2 fK2 Dpt :=
  DCJetKit.mul_mem (JC8MM2_mem) (JINVPI_mem)

theorem op_K2 : dMul ⟨(200 : ℤ), (326716215406560866862089564766435815694404223883942308102128 : ℤ), (326716343961604407581311608123403202987412425660181810725568 : ℤ)⟩ ⟨(201 : ℤ), (1023008531944857192435636399959512221399956651744321939710458 : ℤ), (1023008531945153354587215586928568294839305312105910667096957 : ℤ)⟩ = ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ := by
  rfl

theorem ev_K2 : (JK2).value = ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ := by
  rw [show (JK2).value = dMul (JC8MM2).value (JINVPI).value from rfl, ev_C8MM2, ev_INVPI]
  exact op_K2

def JAsq : DCJet := DCJetKit.mul JA JA
theorem JAsq_mem : JetMem JAsq fAsq Dpt :=
  DCJetKit.mul_mem (JA_mem) (JA_mem)

theorem op_Asq : dMul ⟨(195 : ℤ), (1333910316396662079673904136459211970810824365327380427374985 : ℤ), (1333910316396662080061796216384125113971218103887602859820128 : ℤ)⟩ ⟨(195 : ℤ), (1333910316396662079673904136459211970810824365327380427374985 : ℤ), (1333910316396662080061796216384125113971218103887602859820128 : ℤ)⟩ = ⟨(190 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ := by
  rfl

theorem ev_Asq : (JAsq).value = ⟨(190 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ := by
  rw [show (JAsq).value = dMul (JA).value (JA).value from rfl, ev_A]
  exact op_Asq

def JF4A : DCJet := DCJetKit.mul JC4 JAsq
theorem JF4A_mem : JetMem JF4A fF4A Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JAsq_mem)

theorem op_F4A : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ = ⟨(188 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ := by
  rfl

theorem ev_F4A : (JF4A).value = ⟨(188 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ := by
  rw [show (JF4A).value = dMul (JC4).value (JAsq).value from rfl, ev_C4, ev_Asq]
  exact op_F4A

def JBsq : DCJet := DCJetKit.mul JB JB
theorem JBsq_mem : JetMem JBsq fBsq Dpt :=
  DCJetKit.mul_mem (JB_mem) (JB_mem)

theorem op_Bsq : dMul ⟨(195 : ℤ), (1157571206224324583453867206116242149967746595561963531485836 : ℤ), (1157571206224324583782111823675972761107046395468456588778222 : ℤ)⟩ ⟨(195 : ℤ), (1157571206224324583453867206116242149967746595561963531485836 : ℤ), (1157571206224324583782111823675972761107046395468456588778222 : ℤ)⟩ = ⟨(190 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ := by
  rfl

theorem ev_Bsq : (JBsq).value = ⟨(190 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ := by
  rw [show (JBsq).value = dMul (JB).value (JB).value from rfl, ev_B]
  exact op_Bsq

def JF4B : DCJet := DCJetKit.mul JC4 JBsq
theorem JF4B_mem : JetMem JF4B fF4B Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JBsq_mem)

theorem op_F4B : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ = ⟨(188 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ := by
  rfl

theorem ev_F4B : (JF4B).value = ⟨(188 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ := by
  rw [show (JF4B).value = dMul (JC4).value (JBsq).value from rfl, ev_C4, ev_Bsq]
  exact op_F4B

def JCsq : DCJet := DCJetKit.mul JC JC
theorem JCsq_mem : JetMem JCsq fCsq Dpt :=
  DCJetKit.mul_mem (JC_mem) (JC_mem)

theorem op_Csq : dMul ⟨(195 : ℤ), (1361170153185429100697814861588917636883099871851422868568926 : ℤ), (1361170153185429101094548471504951617548607717919687416618968 : ℤ)⟩ ⟨(195 : ℤ), (1361170153185429100697814861588917636883099871851422868568926 : ℤ), (1361170153185429101094548471504951617548607717919687416618968 : ℤ)⟩ = ⟨(190 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ := by
  rfl

theorem ev_Csq : (JCsq).value = ⟨(190 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ := by
  rw [show (JCsq).value = dMul (JC).value (JC).value from rfl, ev_C]
  exact op_Csq

def JF4C : DCJet := DCJetKit.mul JC4 JCsq
theorem JF4C_mem : JetMem JF4C fF4C Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JCsq_mem)

theorem op_F4C : dMul ⟨(0 : ℤ), (4 : ℤ), (4 : ℤ)⟩ ⟨(190 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ = ⟨(188 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ := by
  rfl

theorem ev_F4C : (JF4C).value = ⟨(188 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ := by
  rw [show (JF4C).value = dMul (JC4).value (JCsq).value from rfl, ev_C4, ev_Csq]
  exact op_F4C

def JD4Asq : DCJet := DCJetKit.mul JD4A JD4A
theorem JD4Asq_mem : JetMem JD4Asq fD4Asq Dpt :=
  DCJetKit.mul_mem (JD4A_mem) (JD4A_mem)

theorem op_D4Asq : dMul ⟨(194 : ℤ), (860963701131141922030125089878323052447174759044553792864966 : ℤ), (860963701131141922030125089878323052447174759044553792864971 : ℤ)⟩ ⟨(194 : ℤ), (860963701131141922030125089878323052447174759044553792864966 : ℤ), (860963701131141922030125089878323052447174759044553792864971 : ℤ)⟩ = ⟨(189 : ℤ), (922572587429469814455283896904277198558750056647521410044152 : ℤ), (922572587429469814455283896904277198558750056647521410044163 : ℤ)⟩ := by
  rfl

theorem ev_D4Asq : (JD4Asq).value = ⟨(189 : ℤ), (922572587429469814455283896904277198558750056647521410044152 : ℤ), (922572587429469814455283896904277198558750056647521410044163 : ℤ)⟩ := by
  rw [show (JD4Asq).value = dMul (JD4A).value (JD4A).value from rfl, ev_D4A]
  exact op_D4Asq

def JD4Bsq : DCJet := DCJetKit.mul JD4B JD4B
theorem JD4Bsq_mem : JetMem JD4Bsq fD4Bsq Dpt :=
  DCJetKit.mul_mem (JD4B_mem) (JD4B_mem)

theorem op_D4Bsq : dMul ⟨(194 : ℤ), (846571070375843029641841532427802576784130360944972505709874 : ℤ), (846571070375843029641841532427802576784130360944972505709878 : ℤ)⟩ ⟨(194 : ℤ), (846571070375843029641841532427802576784130360944972505709874 : ℤ), (846571070375843029641841532427802576784130360944972505709878 : ℤ)⟩ = ⟨(189 : ℤ), (891985325455139711713269145770982657565141967438972128564256 : ℤ), (891985325455139711713269145770982657565141967438972128564266 : ℤ)⟩ := by
  rfl

theorem ev_D4Bsq : (JD4Bsq).value = ⟨(189 : ℤ), (891985325455139711713269145770982657565141967438972128564256 : ℤ), (891985325455139711713269145770982657565141967438972128564266 : ℤ)⟩ := by
  rw [show (JD4Bsq).value = dMul (JD4B).value (JD4B).value from rfl, ev_D4B]
  exact op_D4Bsq

def JD4Csq : DCJet := DCJetKit.mul JD4C JD4C
theorem JD4Csq_mem : JetMem JD4Csq fD4Csq Dpt :=
  DCJetKit.mul_mem (JD4C_mem) (JD4C_mem)

theorem op_D4Csq : dMul ⟨(195 : ℤ), (1390814423445909045931724539666596216202568355072284717613125 : ℤ), (1390814423445909045931724539666596216202568355072284717613135 : ℤ)⟩ ⟨(195 : ℤ), (1390814423445909045931724539666596216202568355072284717613125 : ℤ), (1390814423445909045931724539666596216202568355072284717613135 : ℤ)⟩ = ⟨(190 : ℤ), (1203758145733100049876945885196830347376949172886472067470008 : ℤ), (1203758145733100049876945885196830347376949172886472067470027 : ℤ)⟩ := by
  rfl

theorem ev_D4Csq : (JD4Csq).value = ⟨(190 : ℤ), (1203758145733100049876945885196830347376949172886472067470008 : ℤ), (1203758145733100049876945885196830347376949172886472067470027 : ℤ)⟩ := by
  rw [show (JD4Csq).value = dMul (JD4C).value (JD4C).value from rfl, ev_D4C]
  exact op_D4Csq

def JT4A : DCJet := DCJetKit.inv JF4A
theorem JT4A_mem : JetMem JT4A fT4A Dpt :=
  DCJetKit.inv_mem (JF4A_mem) (by rw [ev_F4A]; decide)

theorem op_T4A : dInv ⟨(188 : ℤ), (1107271520856886614327314788849087738840286714376407858083836 : ℤ), (1107271520856886614971288897134010154156027134826816376199861 : ℤ)⟩ = ⟨(211 : ℤ), (1166041855790067314388406740580414829218446929553365038942749 : ℤ), (1166041855790067315066560879074109214339329776498851132538005 : ℤ)⟩ := by
  rfl

theorem ev_T4A : (JT4A).value = ⟨(211 : ℤ), (1166041855790067314388406740580414829218446929553365038942749 : ℤ), (1166041855790067315066560879074109214339329776498851132538005 : ℤ)⟩ := by
  rw [show (JT4A).value = dInv (JF4A).value from rfl, ev_F4A]
  exact op_T4A

def JT4B : DCJet := DCJetKit.inv JF4B
theorem JT4B_mem : JetMem JT4B fT4B Dpt :=
  DCJetKit.inv_mem (JF4B_mem) (by rw [ev_F4B]; decide)

theorem op_T4B : dInv ⟨(188 : ℤ), (833866061150814718228217401924834950699809288261615682161692 : ℤ), (833866061150814718701124891099968646478943404782775038656756 : ℤ)⟩ = ⟨(211 : ℤ), (1548360101455117024697999928250374869116606644062262133992794 : ℤ), (1548360101455117025576115877600257158957115824903951823968526 : ℤ)⟩ := by
  rfl

theorem ev_T4B : (JT4B).value = ⟨(211 : ℤ), (1548360101455117024697999928250374869116606644062262133992794 : ℤ), (1548360101455117025576115877600257158957115824903951823968526 : ℤ)⟩ := by
  rw [show (JT4B).value = dInv (JF4B).value from rfl, ev_F4B]
  exact op_T4B

def JT4C : DCJet := DCJetKit.inv JF4C
theorem JT4C_mem : JetMem JT4C fT4C Dpt :=
  DCJetKit.inv_mem (JF4C_mem) (by rw [ev_F4C]; decide)

theorem op_T4C : dInv ⟨(188 : ℤ), (1152990429557737955154775269094943166763125400590124466897512 : ℤ), (1152990429557737955826888236377682893723941250974959374736774 : ℤ)⟩ = ⟨(211 : ℤ), (1119805425912079540476305549263420692437624113448548456530604 : ℤ), (1119805425912079541129073974997686882519342806371213899764689 : ℤ)⟩ := by
  rfl

theorem ev_T4C : (JT4C).value = ⟨(211 : ℤ), (1119805425912079540476305549263420692437624113448548456530604 : ℤ), (1119805425912079541129073974997686882519342806371213899764689 : ℤ)⟩ := by
  rw [show (JT4C).value = dInv (JF4C).value from rfl, ev_F4C]
  exact op_T4C

def JTA : DCJet := DCJetKit.mul JDlt JT4A
theorem JTA_mem : JetMem JTA fTA Dpt :=
  DCJetKit.mul_mem (JDlt_mem) (JT4A_mem)

theorem op_TA : dMul ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ ⟨(211 : ℤ), (1166041855790067314388406740580414829218446929553365038942749 : ℤ), (1166041855790067315066560879074109214339329776498851132538005 : ℤ)⟩ = ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ := by
  rfl

theorem ev_TA : (JTA).value = ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ := by
  rw [show (JTA).value = dMul (JDlt).value (JT4A).value from rfl, ev_Dlt, ev_T4A]
  exact op_TA

def JTB : DCJet := DCJetKit.mul JDlt JT4B
theorem JTB_mem : JetMem JTB fTB Dpt :=
  DCJetKit.mul_mem (JDlt_mem) (JT4B_mem)

theorem op_TB : dMul ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ ⟨(211 : ℤ), (1548360101455117024697999928250374869116606644062262133992794 : ℤ), (1548360101455117025576115877600257158957115824903951823968526 : ℤ)⟩ = ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ := by
  rfl

theorem ev_TB : (JTB).value = ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ := by
  rw [show (JTB).value = dMul (JDlt).value (JT4B).value from rfl, ev_Dlt, ev_T4B]
  exact op_TB

def JTC : DCJet := DCJetKit.mul JDlt JT4C
theorem JTC_mem : JetMem JTC fTC Dpt :=
  DCJetKit.mul_mem (JDlt_mem) (JT4C_mem)

theorem op_TC : dMul ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ ⟨(211 : ℤ), (1119805425912079540476305549263420692437624113448548456530604 : ℤ), (1119805425912079541129073974997686882519342806371213899764689 : ℤ)⟩ = ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ := by
  rfl

theorem ev_TC : (JTC).value = ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ := by
  rw [show (JTC).value = dMul (JDlt).value (JT4C).value from rfl, ev_Dlt, ev_T4C]
  exact op_TC

def JInvA2A : DCJet := DCJetKit.inv JD4Asq
theorem JInvA2A_mem : JetMem JInvA2A fInvA2A Dpt :=
  DCJetKit.inv_mem (JD4Asq_mem) (by rw [ev_D4Asq]; decide)

theorem op_InvA2A : dInv ⟨(189 : ℤ), (922572587429469814455283896904277198558750056647521410044152 : ℤ), (922572587429469814455283896904277198558750056647521410044163 : ℤ)⟩ = ⟨(210 : ℤ), (1399483310728826648992968599075806684134865074156246712213241 : ℤ), (1399483310728826648992968599075806684134865074156246712213259 : ℤ)⟩ := by
  rfl

theorem ev_InvA2A : (JInvA2A).value = ⟨(210 : ℤ), (1399483310728826648992968599075806684134865074156246712213241 : ℤ), (1399483310728826648992968599075806684134865074156246712213259 : ℤ)⟩ := by
  rw [show (JInvA2A).value = dInv (JD4Asq).value from rfl, ev_D4Asq]
  exact op_InvA2A

def JInvA2B : DCJet := DCJetKit.inv JD4Bsq
theorem JInvA2B_mem : JetMem JInvA2B fInvA2B Dpt :=
  DCJetKit.inv_mem (JD4Bsq_mem) (by rw [ev_D4Bsq]; decide)

theorem op_InvA2B : dInv ⟨(189 : ℤ), (891985325455139711713269145770982657565141967438972128564256 : ℤ), (891985325455139711713269145770982657565141967438972128564266 : ℤ)⟩ = ⟨(210 : ℤ), (1447473296026088451804955645658995768785473701931245412515215 : ℤ), (1447473296026088451804955645658995768785473701931245412515232 : ℤ)⟩ := by
  rfl

theorem ev_InvA2B : (JInvA2B).value = ⟨(210 : ℤ), (1447473296026088451804955645658995768785473701931245412515215 : ℤ), (1447473296026088451804955645658995768785473701931245412515232 : ℤ)⟩ := by
  rw [show (JInvA2B).value = dInv (JD4Bsq).value from rfl, ev_D4Bsq]
  exact op_InvA2B

def JInvA2C : DCJet := DCJetKit.inv JD4Csq
theorem JInvA2C_mem : JetMem JInvA2C fInvA2C Dpt :=
  DCJetKit.inv_mem (JD4Csq_mem) (by rw [ev_D4Csq]; decide)

theorem op_InvA2C : dInv ⟨(190 : ℤ), (1203758145733100049876945885196830347376949172886472067470008 : ℤ), (1203758145733100049876945885196830347376949172886472067470027 : ℤ)⟩ = ⟨(209 : ℤ), (1072578361043735280270825814950951686808969151192827470670001 : ℤ), (1072578361043735280270825814950951686808969151192827470670019 : ℤ)⟩ := by
  rfl

theorem ev_InvA2C : (JInvA2C).value = ⟨(209 : ℤ), (1072578361043735280270825814950951686808969151192827470670001 : ℤ), (1072578361043735280270825814950951686808969151192827470670019 : ℤ)⟩ := by
  rw [show (JInvA2C).value = dInv (JD4Csq).value from rfl, ev_D4Csq]
  exact op_InvA2C

def JKDltA : DCJet := DCJetKit.mul JKA JDlt
theorem JKDltA_mem : JetMem JKDltA fKDltA Dpt :=
  DCJetKit.mul_mem (JKA_mem) (JDlt_mem)

theorem op_KDltA : dMul ⟨(195 : ℤ), (1062617682908738286177750025285228736473916835637922788191434 : ℤ), (1062617682908738286177750025285228736473916835637922788191435 : ℤ)⟩ ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ = ⟨(192 : ℤ), (1231272563514791608454685842548256249982358856005330781499870 : ℤ), (1231272563514791608454685842548256249982358856005330781500274 : ℤ)⟩ := by
  rfl

theorem ev_KDltA : (JKDltA).value = ⟨(192 : ℤ), (1231272563514791608454685842548256249982358856005330781499870 : ℤ), (1231272563514791608454685842548256249982358856005330781500274 : ℤ)⟩ := by
  rw [show (JKDltA).value = dMul (JKA).value (JDlt).value from rfl, ev_KA, ev_Dlt]
  exact op_KDltA

def JKDltB : DCJet := DCJetKit.mul JKB JDlt
theorem JKDltB_mem : JetMem JKDltB fKDltB Dpt :=
  DCJetKit.mul_mem (JKB_mem) (JDlt_mem)

theorem op_KDltB : dMul ⟨(195 : ℤ), (1089018126297810550270041468458448172708180880710620844476543 : ℤ), (1089018126297810550270041468458448172708180880710620844476544 : ℤ)⟩ ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ = ⟨(192 : ℤ), (1261863190917687832045002412896315942428002554524161573010804 : ℤ), (1261863190917687832045002412896315942428002554524161573011218 : ℤ)⟩ := by
  rfl

theorem ev_KDltB : (JKDltB).value = ⟨(192 : ℤ), (1261863190917687832045002412896315942428002554524161573010804 : ℤ), (1261863190917687832045002412896315942428002554524161573011218 : ℤ)⟩ := by
  rw [show (JKDltB).value = dMul (JKB).value (JDlt).value from rfl, ev_KB, ev_Dlt]
  exact op_KDltB

def JKDltC : DCJet := DCJetKit.mul JKC JDlt
theorem JKDltC_mem : JetMem JKDltC fKDltC Dpt :=
  DCJetKit.mul_mem (JKC_mem) (JDlt_mem)

theorem op_KDltC : dMul ⟨(195 : ℤ), (1275587419533100335972672666670339781884105661844125783276124 : ℤ), (1275587419533100335972672666670339781884105661844125783276125 : ℤ)⟩ ⟨(192 : ℤ), (58187047096873781077357688684419106980752784188892137221393 : ℤ), (58187047096873781077357688684419106980752784188892137221412 : ℤ)⟩ = ⟨(192 : ℤ), (1478044095536312706645163099097857047557673886737115555504278 : ℤ), (1478044095536312706645163099097857047557673886737115555504763 : ℤ)⟩ := by
  rfl

theorem ev_KDltC : (JKDltC).value = ⟨(192 : ℤ), (1478044095536312706645163099097857047557673886737115555504278 : ℤ), (1478044095536312706645163099097857047557673886737115555504763 : ℤ)⟩ := by
  rw [show (JKDltC).value = dMul (JKC).value (JDlt).value from rfl, ev_KC, ev_Dlt]
  exact op_KDltC

def JGA : DCJet := DCJetKit.mul JKDltA JInvA2A
theorem JGA_mem : JetMem JGA fGA Dpt :=
  DCJetKit.mul_mem (JKDltA_mem) (JInvA2A_mem)

theorem op_GA : dMul ⟨(192 : ℤ), (1231272563514791608454685842548256249982358856005330781499870 : ℤ), (1231272563514791608454685842548256249982358856005330781500274 : ℤ)⟩ ⟨(210 : ℤ), (1399483310728826648992968599075806684134865074156246712213241 : ℤ), (1399483310728826648992968599075806684134865074156246712213259 : ℤ)⟩ = ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ := by
  rfl

theorem ev_GA : (JGA).value = ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ := by
  rw [show (JGA).value = dMul (JKDltA).value (JInvA2A).value from rfl, ev_KDltA, ev_InvA2A]
  exact op_GA

def JGB : DCJet := DCJetKit.mul JKDltB JInvA2B
theorem JGB_mem : JetMem JGB fGB Dpt :=
  DCJetKit.mul_mem (JKDltB_mem) (JInvA2B_mem)

theorem op_GB : dMul ⟨(192 : ℤ), (1261863190917687832045002412896315942428002554524161573010804 : ℤ), (1261863190917687832045002412896315942428002554524161573011218 : ℤ)⟩ ⟨(210 : ℤ), (1447473296026088451804955645658995768785473701931245412515215 : ℤ), (1447473296026088451804955645658995768785473701931245412515232 : ℤ)⟩ = ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ := by
  rfl

theorem ev_GB : (JGB).value = ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ := by
  rw [show (JGB).value = dMul (JKDltB).value (JInvA2B).value from rfl, ev_KDltB, ev_InvA2B]
  exact op_GB

def JGC : DCJet := DCJetKit.mul JKDltC JInvA2C
theorem JGC_mem : JetMem JGC fGC Dpt :=
  DCJetKit.mul_mem (JKDltC_mem) (JInvA2C_mem)

theorem op_GC : dMul ⟨(192 : ℤ), (1478044095536312706645163099097857047557673886737115555504278 : ℤ), (1478044095536312706645163099097857047557673886737115555504763 : ℤ)⟩ ⟨(209 : ℤ), (1072578361043735280270825814950951686808969151192827470670001 : ℤ), (1072578361043735280270825814950951686808969151192827470670019 : ℤ)⟩ = ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ := by
  rfl

theorem ev_GC : (JGC).value = ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ := by
  rw [show (JGC).value = dMul (JKDltC).value (JInvA2C).value from rfl, ev_KDltC, ev_InvA2C]
  exact op_GC

def JInvD4A : DCJet := DCJetKit.inv JD4A
theorem JInvD4A_mem : JetMem JInvD4A fInvD4A Dpt :=
  DCJetKit.inv_mem (JD4A_mem) (by rw [ev_D4A]; decide)

theorem op_InvD4A : dInv ⟨(194 : ℤ), (860963701131141922030125089878323052447174759044553792864966 : ℤ), (860963701131141922030125089878323052447174759044553792864971 : ℤ)⟩ = ⟨(205 : ℤ), (1499627611880922082540212705637646927833492748836040420490945 : ℤ), (1499627611880922082540212705637646927833492748836040420490954 : ℤ)⟩ := by
  rfl

theorem ev_InvD4A : (JInvD4A).value = ⟨(205 : ℤ), (1499627611880922082540212705637646927833492748836040420490945 : ℤ), (1499627611880922082540212705637646927833492748836040420490954 : ℤ)⟩ := by
  rw [show (JInvD4A).value = dInv (JD4A).value from rfl, ev_D4A]
  exact op_InvD4A

def JInvD4B : DCJet := DCJetKit.inv JD4B
theorem JInvD4B_mem : JetMem JInvD4B fInvD4B Dpt :=
  DCJetKit.inv_mem (JD4B_mem) (by rw [ev_D4B]; decide)

theorem op_InvD4B : dInv ⟨(194 : ℤ), (846571070375843029641841532427802576784130360944972505709874 : ℤ), (846571070375843029641841532427802576784130360944972505709878 : ℤ)⟩ = ⟨(205 : ℤ), (1525122915516410781299287051604437836469493616951516602010447 : ℤ), (1525122915516410781299287051604437836469493616951516602010455 : ℤ)⟩ := by
  rfl

theorem ev_InvD4B : (JInvD4B).value = ⟨(205 : ℤ), (1525122915516410781299287051604437836469493616951516602010447 : ℤ), (1525122915516410781299287051604437836469493616951516602010455 : ℤ)⟩ := by
  rw [show (JInvD4B).value = dInv (JD4B).value from rfl, ev_D4B]
  exact op_InvD4B

def JInvD4C : DCJet := DCJetKit.inv JD4C
theorem JInvD4C_mem : JetMem JInvD4C fInvD4C Dpt :=
  DCJetKit.inv_mem (JD4C_mem) (by rw [ev_D4C]; decide)

theorem op_InvD4C : dInv ⟨(195 : ℤ), (1390814423445909045931724539666596216202568355072284717613125 : ℤ), (1390814423445909045931724539666596216202568355072284717613135 : ℤ)⟩ = ⟨(204 : ℤ), (928322943218073527916713246147134755739465969164950934054665 : ℤ), (928322943218073527916713246147134755739465969164950934054673 : ℤ)⟩ := by
  rfl

theorem ev_InvD4C : (JInvD4C).value = ⟨(204 : ℤ), (928322943218073527916713246147134755739465969164950934054665 : ℤ), (928322943218073527916713246147134755739465969164950934054673 : ℤ)⟩ := by
  rw [show (JInvD4C).value = dInv (JD4C).value from rfl, ev_D4C]
  exact op_InvD4C

def JIA : DCJet := DCJetKit.inv JA
theorem JIA_mem : JetMem JIA fIA Dpt :=
  DCJetKit.inv_mem (JA_mem) (by rw [ev_A]; decide)

theorem op_IA : dInv ⟨(195 : ℤ), (1333910316396662079673904136459211970810824365327380427374985 : ℤ), (1333910316396662080061796216384125113971218103887602859820128 : ℤ)⟩ = ⟨(204 : ℤ), (967924847100076862763948394385695756474911542319661092148748 : ℤ), (967924847100076863045414380170159443577058772719079183650758 : ℤ)⟩ := by
  rfl

theorem ev_IA : (JIA).value = ⟨(204 : ℤ), (967924847100076862763948394385695756474911542319661092148748 : ℤ), (967924847100076863045414380170159443577058772719079183650758 : ℤ)⟩ := by
  rw [show (JIA).value = dInv (JA).value from rfl, ev_A]
  exact op_IA

def JIB : DCJet := DCJetKit.inv JB
theorem JIB_mem : JetMem JIB fIB Dpt :=
  DCJetKit.inv_mem (JB_mem) (by rw [ev_B]; decide)

theorem op_IB : dInv ⟨(195 : ℤ), (1157571206224324583453867206116242149967746595561963531485836 : ℤ), (1157571206224324583782111823675972761107046395468456588778222 : ℤ)⟩ = ⟨(204 : ℤ), (1115374097162234065383872961265915749158488237767651560879466 : ℤ), (1115374097162234065700152030743822374104406456533700622276905 : ℤ)⟩ := by
  rfl

theorem ev_IB : (JIB).value = ⟨(204 : ℤ), (1115374097162234065383872961265915749158488237767651560879466 : ℤ), (1115374097162234065700152030743822374104406456533700622276905 : ℤ)⟩ := by
  rw [show (JIB).value = dInv (JB).value from rfl, ev_B]
  exact op_IB

def JIC : DCJet := DCJetKit.inv JC
theorem JIC_mem : JetMem JIC fIC Dpt :=
  DCJetKit.inv_mem (JC_mem) (by rw [ev_C]; decide)

theorem op_IC : dInv ⟨(195 : ℤ), (1361170153185429100697814861588917636883099871851422868568926 : ℤ), (1361170153185429101094548471504951617548607717919687416618968 : ℤ)⟩ = ⟨(204 : ℤ), (948540442223145994352916239637870076727879857974802803369000 : ℤ), (948540442223145994629382685007595316690136029017825511694095 : ℤ)⟩ := by
  rfl

theorem ev_IC : (JIC).value = ⟨(204 : ℤ), (948540442223145994352916239637870076727879857974802803369000 : ℤ), (948540442223145994629382685007595316690136029017825511694095 : ℤ)⟩ := by
  rw [show (JIC).value = dInv (JC).value from rfl, ev_C]
  exact op_IC

def JWA : DCJet := DCJetKit.mul JNA JInvD4A
theorem JWA_mem : JetMem JWA fWA Dpt :=
  DCJetKit.mul_mem (JNA_mem) (JInvD4A_mem)

theorem op_WA : dMul ⟨(197 : ℤ), (924002375854193293369886881650263824940254859093736207193854 : ℤ), (924002375854193293369886881650263824940254859093736207193855 : ℤ)⟩ ⟨(205 : ℤ), (1499627611880922082540212705637646927833492748836040420490945 : ℤ), (1499627611880922082540212705637646927833492748836040420490954 : ℤ)⟩ = ⟨(202 : ℤ), (862298009076941905488898486797240865218360403741950246774509 : ℤ), (862298009076941905488898486797240865218360403741950246774516 : ℤ)⟩ := by
  rfl

theorem ev_WA : (JWA).value = ⟨(202 : ℤ), (862298009076941905488898486797240865218360403741950246774509 : ℤ), (862298009076941905488898486797240865218360403741950246774516 : ℤ)⟩ := by
  rw [show (JWA).value = dMul (JNA).value (JInvD4A).value from rfl, ev_NA, ev_InvD4A]
  exact op_WA

def JWB : DCJet := DCJetKit.mul JNB JInvD4B
theorem JWB_mem : JetMem JWB fWB Dpt :=
  DCJetKit.mul_mem (JNB_mem) (JInvD4B_mem)

theorem op_WB : dMul ⟨(197 : ℤ), (935410246372038024334603224631577854991336249552941141504637 : ℤ), (935410246372038024334603224631577854991336249552941141504638 : ℤ)⟩ ⟨(205 : ℤ), (1525122915516410781299287051604437836469493616951516602010447 : ℤ), (1525122915516410781299287051604437836469493616951516602010455 : ℤ)⟩ = ⟨(202 : ℤ), (887785068781979153106968947565936126465625777824364717987848 : ℤ), (887785068781979153106968947565936126465625777824364717987854 : ℤ)⟩ := by
  rfl

theorem ev_WB : (JWB).value = ⟨(202 : ℤ), (887785068781979153106968947565936126465625777824364717987848 : ℤ), (887785068781979153106968947565936126465625777824364717987854 : ℤ)⟩ := by
  rw [show (JWB).value = dMul (JNB).value (JInvD4B).value from rfl, ev_NB, ev_InvD4B]
  exact op_WB

def JWC : DCJet := DCJetKit.mul JNC JInvD4C
theorem JWC_mem : JetMem JWC fWC Dpt :=
  DCJetKit.mul_mem (JNC_mem) (JInvD4C_mem)

theorem op_WC : dMul ⟨(197 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ), (1012370967883288419324556411216238319360954787890667969582900 : ℤ)⟩ ⟨(204 : ℤ), (928322943218073527916713246147134755739465969164950934054665 : ℤ), (928322943218073527916713246147134755739465969164950934054673 : ℤ)⟩ = ⟨(202 : ℤ), (1169686908454916544514486923722952161952012388506325351528758 : ℤ), (1169686908454916544514486923722952161952012388506325351528769 : ℤ)⟩ := by
  rfl

theorem ev_WC : (JWC).value = ⟨(202 : ℤ), (1169686908454916544514486923722952161952012388506325351528758 : ℤ), (1169686908454916544514486923722952161952012388506325351528769 : ℤ)⟩ := by
  rw [show (JWC).value = dMul (JNC).value (JInvD4C).value from rfl, ev_NC, ev_InvD4C]
  exact op_WC

theorem mv_MtA : dMatan9 ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ = ⟨(200 : ℤ), (1605182242761259241746093515178406056464391573641090454600878 : ℤ), (1605182242761315071727396218558088168198853459004420340546532 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtAa : dAdd ONE ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ = ⟨(199 : ℤ), (806107912464369165491315644841482670384796380133662887680229 : ℤ), (806107912464369165492850387692041223264813782970119602210100 : ℤ)⟩ := by rfl
theorem mdMtAb : dInv ⟨(199 : ℤ), (806107912464369165491315644841482670384796380133662887680229 : ℤ), (806107912464369165492850387692041223264813782970119602210100 : ℤ)⟩ = ⟨(200 : ℤ), (1601677541033345708818280653453390389395747756028777328396900 : ℤ), (1601677541033345708821330075394289380373104932544612800534922 : ℤ)⟩ := by rfl
theorem mdMtAc : dSub ⟨(200 : ℤ), (1601677541033345708818280653453390389395747756028777328396900 : ℤ), (1601677541033345708821330075394289380373104932544612800534922 : ℤ)⟩ ⟨(200 : ℤ), (1605182242761259241746093515178406056464391573641090454600878 : ℤ), (1605182242761315071727396218558088168198853459004420340546532 : ℤ)⟩ = ⟨(200 : ℤ), (-3504701727969362909115565104697778803105702975643012149632 : ℤ), (-3504701727913532924763439784116676091286641096477654065956 : ℤ)⟩ := by rfl
theorem mdMtAd : dMul (dInt 2) ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ = ⟨(207 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ := by rfl
theorem mdMtAe : dInv ⟨(207 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ = ⟨(192 : ℤ), (955601816128378827591312189619015553893640363460408008647056 : ℤ), (955601816128378828147077253404361990553708316106706056108442 : ℤ)⟩ := by rfl
theorem mdMtAf : dMul ⟨(200 : ℤ), (-3504701727969362909115565104697778803105702975643012149632 : ℤ), (-3504701727913532924763439784116676091286641096477654065956 : ℤ)⟩ ⟨(192 : ℤ), (955601816128378827591312189619015553893640363460408008647056 : ℤ), (955601816128378828147077253404361990553708316106706056108442 : ℤ)⟩ = ⟨(201 : ℤ), (-1067084612427260633732655369796273686783128946328771186836568 : ℤ), (-1067084612410261949104577034227330284257826667015686820889185 : ℤ)⟩ := by rfl

theorem md_MtA : dMatanD ⟨(208 : ℤ), (1351111851455502192811314519501500991331780220040432655125395 : ℤ), (1351111851455502193597102858987480065900690472306270494418441 : ℤ)⟩ ⟨(200 : ℤ), (1605182242761259241746093515178406056464391573641090454600878 : ℤ), (1605182242761315071727396218558088168198853459004420340546532 : ℤ)⟩ = ⟨(201 : ℤ), (-1067084612427260633732655369796273686783128946328771186836568 : ℤ), (-1067084612410261949104577034227330284257826667015686820889185 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtAa, mdMtAb, mdMtAc, mdMtAd, mdMtAe]
  exact mdMtAf

theorem PMtA_gates : (dLoBig JTA.value = true ∧
    dLoBig (dAdd ONE JTA.value) = true ∧
    dLoBig (dMul (dInt 2) JTA.value) = true) := by
  rw [ev_TA]
  decide
theorem PMtA_hbig : dLoBig JTA.value = true := PMtA_gates.1
theorem PMtA_hden1 : dLoBig (dAdd ONE JTA.value) = true :=
  PMtA_gates.2.1
theorem PMtA_hden2 : dLoBig (dMul (dInt 2) JTA.value) = true :=
  PMtA_gates.2.2

def JMtA : DCJet := DCJetKit.matan9 JTA
theorem JMtA_mem : JetMem JMtA fMtA Dpt :=
  DCJetKit.matan9_mem (JTA_mem) PMtA_hbig PMtA_hden1 PMtA_hden2

theorem ev_MtA : (JMtA).value = ⟨(200 : ℤ), (1605182242761259241746093515178406056464391573641090454600878 : ℤ), (1605182242761315071727396218558088168198853459004420340546532 : ℤ)⟩ := by
  rw [show (JMtA).value = dMatan9 (JTA).value from rfl, ev_TA]
  exact mv_MtA

theorem mv_MtB : dMatan9 ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ = ⟨(200 : ℤ), (1604608057110327246095012691423460250813592981886360387245682 : ℤ), (1604608057110557738508792275723676423463570473706786127157132 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtBa : dAdd ONE ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ = ⟨(199 : ℤ), (806973143775167955684673559110754438999155161049702614109030 : ℤ), (806973143775167955686660839138595335538468203377988203371797 : ℤ)⟩ := by rfl
theorem mdMtBb : dInv ⟨(199 : ℤ), (806973143775167955684673559110754438999155161049702614109030 : ℤ), (806973143775167955686660839138595335538468203377988203371797 : ℤ)⟩ = ⟨(200 : ℤ), (1599960232881277427996666263594636174121557483049899576478833 : ℤ), (1599960232881277428000606381107432234399142902387157186764837 : ℤ)⟩ := by rfl
theorem mdMtBc : dSub ⟨(200 : ℤ), (1599960232881277427996666263594636174121557483049899576478833 : ℤ), (1599960232881277428000606381107432234399142902387157186764837 : ℤ)⟩ ⟨(200 : ℤ), (1604608057110327246095012691423460250813592981886360387245682 : ℤ), (1604608057110557738508792275723676423463570473706786127157132 : ℤ)⟩ = ⟨(200 : ℤ), (-4647824229280310512126012129040249342012990656886550678299 : ℤ), (-4647824229049818094406310316028016414450079499203200480845 : ℤ)⟩ := by rfl
theorem mdMtBd : dMul (dInt 2) ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ = ⟨(206 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ := by rfl
theorem mdMtBe : dInv ⟨(206 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ = ⟨(193 : ℤ), (1439292725287255661950872977958109603600715615256411178091022 : ℤ), (1439292725287255662767133934740864870197317020933293929466861 : ℤ)⟩ := by rfl
theorem mdMtBf : dMul ⟨(200 : ℤ), (-4647824229280310512126012129040249342012990656886550678299 : ℤ), (-4647824229049818094406310316028016414450079499203200480845 : ℤ)⟩ ⟨(193 : ℤ), (1439292725287255661950872977958109603600715615256411178091022 : ℤ), (1439292725287255662767133934740864870197317020933293929466861 : ℤ)⟩ = ⟨(201 : ℤ), (-1065711515221269006964198228540216565664555685768487926587077 : ℤ), (-1065711515168418809876984784095953485131871506996177628365686 : ℤ)⟩ := by rfl

theorem md_MtB : dMatanD ⟨(207 : ℤ), (897055141292241385905283312684323260941738024526386293335749 : ℤ), (897055141292241386414026999811592775005876860567497144603858 : ℤ)⟩ ⟨(200 : ℤ), (1604608057110327246095012691423460250813592981886360387245682 : ℤ), (1604608057110557738508792275723676423463570473706786127157132 : ℤ)⟩ = ⟨(201 : ℤ), (-1065711515221269006964198228540216565664555685768487926587077 : ℤ), (-1065711515168418809876984784095953485131871506996177628365686 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtBa, mdMtBb, mdMtBc, mdMtBd, mdMtBe]
  exact mdMtBf

theorem PMtB_gates : (dLoBig JTB.value = true ∧
    dLoBig (dAdd ONE JTB.value) = true ∧
    dLoBig (dMul (dInt 2) JTB.value) = true) := by
  rw [ev_TB]
  decide
theorem PMtB_hbig : dLoBig JTB.value = true := PMtB_gates.1
theorem PMtB_hden1 : dLoBig (dAdd ONE JTB.value) = true :=
  PMtB_gates.2.1
theorem PMtB_hden2 : dLoBig (dMul (dInt 2) JTB.value) = true :=
  PMtB_gates.2.2

def JMtB : DCJet := DCJetKit.matan9 JTB
theorem JMtB_mem : JetMem JMtB fMtB Dpt :=
  DCJetKit.matan9_mem (JTB_mem) PMtB_hbig PMtB_hden1 PMtB_hden2

theorem ev_MtB : (JMtB).value = ⟨(200 : ℤ), (1604608057110327246095012691423460250813592981886360387245682 : ℤ), (1604608057110557738508792275723676423463570473706786127157132 : ℤ)⟩ := by
  rw [show (JMtB).value = dMatan9 (JTB).value from rfl, ev_TB]
  exact mv_MtB

theorem mv_MtC : dMatan9 ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ = ⟨(200 : ℤ), (1605251733199857052774616656595705386110349385239744270371750 : ℤ), (1605251733199902657476537645125142932294344243029767474757772 : ℤ)⟩ := by
  unfold dMatan9
  rfl

theorem mdMtCa : dAdd ONE ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ = ⟨(199 : ℤ), (806003273966773012563707348069355487953497049721494879494844 : ℤ), (806003273966773012565184640055940248659391302111666965577924 : ℤ)⟩ := by rfl
theorem mdMtCb : dInv ⟨(199 : ℤ), (806003273966773012563707348069355487953497049721494879494844 : ℤ), (806003273966773012565184640055940248659391302111666965577924 : ℤ)⟩ = ⟨(200 : ℤ), (1601885477076461755720848832518518219915293901204876384761217 : ℤ), (1601885477076461755723784865975386186546013529617012190155573 : ℤ)⟩ := by rfl
theorem mdMtCc : dSub ⟨(200 : ℤ), (1601885477076461755720848832518518219915293901204876384761217 : ℤ), (1601885477076461755723784865975386186546013529617012190155573 : ℤ)⟩ ⟨(200 : ℤ), (1605251733199857052774616656595705386110349385239744270371750 : ℤ), (1605251733199902657476537645125142932294344243029767474757772 : ℤ)⟩ = ⟨(200 : ℤ), (-3366256123440901755688812606624712379050341824891089996555 : ℤ), (-3366256123395297050831790620319199564335855622732080216177 : ℤ)⟩ := by rfl
theorem mdMtCd : dMul (dInt 2) ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ = ⟨(207 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ := by rfl
theorem mdMtCe : dInv ⟨(207 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ = ⟨(192 : ℤ), (995058328251197018428948276403042032254119902376369133906283 : ℤ), (995058328251197019008997848780540759098655978024989525930078 : ℤ)⟩ := by rfl
theorem mdMtCf : dMul ⟨(200 : ℤ), (-3366256123440901755688812606624712379050341824891089996555 : ℤ), (-3366256123395297050831790620319199564335855622732080216177 : ℤ)⟩ ⟨(192 : ℤ), (995058328251197018428948276403042032254119902376369133906283 : ℤ), (995058328251197019008997848780540759098655978024989525930078 : ℤ)⟩ = ⟨(201 : ℤ), (-1067250884838531653201004298029352478886893507632799373402212 : ℤ), (-1067250884824072960243332322895949504138999297108043254110817 : ℤ)⟩ := by rfl

theorem md_MtC : dMatanD ⟨(208 : ℤ), (1297536940686271893875866572172383586506523049010412464207961 : ℤ), (1297536940686271894632240069303781067924380272778520538744660 : ℤ)⟩ ⟨(200 : ℤ), (1605251733199857052774616656595705386110349385239744270371750 : ℤ), (1605251733199902657476537645125142932294344243029767474757772 : ℤ)⟩ = ⟨(201 : ℤ), (-1067250884838531653201004298029352478886893507632799373402212 : ℤ), (-1067250884824072960243332322895949504138999297108043254110817 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMtCa, mdMtCb, mdMtCc, mdMtCd, mdMtCe]
  exact mdMtCf

theorem PMtC_gates : (dLoBig JTC.value = true ∧
    dLoBig (dAdd ONE JTC.value) = true ∧
    dLoBig (dMul (dInt 2) JTC.value) = true) := by
  rw [ev_TC]
  decide
theorem PMtC_hbig : dLoBig JTC.value = true := PMtC_gates.1
theorem PMtC_hden1 : dLoBig (dAdd ONE JTC.value) = true :=
  PMtC_gates.2.1
theorem PMtC_hden2 : dLoBig (dMul (dInt 2) JTC.value) = true :=
  PMtC_gates.2.2

def JMtC : DCJet := DCJetKit.matan9 JTC
theorem JMtC_mem : JetMem JMtC fMtC Dpt :=
  DCJetKit.matan9_mem (JTC_mem) PMtC_hbig PMtC_hden1 PMtC_hden2

theorem ev_MtC : (JMtC).value = ⟨(200 : ℤ), (1605251733199857052774616656595705386110349385239744270371750 : ℤ), (1605251733199902657476537645125142932294344243029767474757772 : ℤ)⟩ := by
  rw [show (JMtC).value = dMatan9 (JTC).value from rfl, ev_TC]
  exact mv_MtC

/-- literal square root `dSqrt ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgA : dSqrt ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(201 : ℤ), (1312686331001145928601832174357245198761615690244911536948482 : ℤ), (1312686331001145928601832174357245198761615690244911536948707 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1312686331001145928601832174357245198761615690244911536948482 : ℤ)) (rhi := (1312686331001145928601832174357245198761615690244911536948706 : ℤ))
    (nlo := 1723145403597250050623855386821889463501497752763073420573485021004982728696391817316510853462922357575912280292855906304) (nhi := 1723145403597250050623855386821889463501497752763073420574074767267225778127515717404400060138048006074630565263411511296) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgA : dSqrt (dInv ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩) = ⟨(199 : ℤ), (1967149209299303945530999479352072042458669319706508663801783 : ℤ), (1967149209299303945530999479352072042458669319706508663802122 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩)) (K := (199 : ℤ))
    (rlo := (1967149209299303945530999479352072042458669319706508663801783 : ℤ)) (rhi := (1967149209299303945530999479352072042458669319706508663802121 : ℤ))
    (nlo := 3869676011646876720493352273384104204875174394442799297331893333784748153024093795108040602879677978824686110214463684608) (nhi := 3869676011646876720493352273384104204875174394442799297333220664609306078991691455796314403189361318497550697096422621184) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem u9_MgA : dMatanU9 (dInv ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩) = ⟨(201 : ℤ), (1552945009839167130104357311594983319435190611759664134261429 : ℤ), (1552951308068909199309257793444596497961015814205144832399512 : ℤ)⟩ := by
  unfold dMatanU9
  rw [sqi_MgA]
  rfl

theorem mt_MgA : DCJetKit.dMatanTight ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(201 : ℤ), (1552945009839167130104357311594983319435190611759664134261429 : ℤ), (1552951308068909199309257793444596497961015814205144832399512 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_neg (by decide)]
  exact u9_MgA

theorem mMgAa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgAb : dInv ⟨(201 : ℤ), (1312686331001145928601832174357245198761615690244911536948482 : ℤ), (1312686331001145928601832174357245198761615690244911536948707 : ℤ)⟩ = ⟨(198 : ℤ), (983574604649651972765499739676036021229334659853254331900892 : ℤ), (983574604649651972765499739676036021229334659853254331901061 : ℤ)⟩ := by rfl
theorem mMgAc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(198 : ℤ), (983574604649651972765499739676036021229334659853254331900892 : ℤ), (983574604649651972765499739676036021229334659853254331901061 : ℤ)⟩ = ⟨(198 : ℤ), (1544995376112131113515323800887768717522048692380576229181833 : ℤ), (1544995376112578391461187431396145845029530127194734018815133 : ℤ)⟩ := by rfl
theorem mMgAd : dInv ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(197 : ℤ), (1204052647042564158386490734378486026990721114622037083239929 : ℤ), (1204052647042564158386490734378486026990721114622037083240342 : ℤ)⟩ := by rfl
theorem mMgAe : dMul ⟨(201 : ℤ), (1552945009839167130104357311594983319435190611759664134261429 : ℤ), (1552951308068909199309257793444596497961015814205144832399512 : ℤ)⟩ ⟨(197 : ℤ), (1204052647042564158386490734378486026990721114622037083239929 : ℤ), (1204052647042564158386490734378486026990721114622037083240342 : ℤ)⟩ = ⟨(198 : ℤ), (1163596540942327603442763551716796225924536768603330130733434 : ℤ), (1163601260103853284774707948229290281394273200215973610405429 : ℤ)⟩ := by rfl
theorem mMgAf : dSub ⟨(198 : ℤ), (1544995376112131113515323800887768717522048692380576229181833 : ℤ), (1544995376112578391461187431396145845029530127194734018815133 : ℤ)⟩ ⟨(198 : ℤ), (1163596540942327603442763551716796225924536768603330130733434 : ℤ), (1163601260103853284774707948229290281394273200215973610405429 : ℤ)⟩ = ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ := by rfl

theorem mv_MgA : dMatanMir ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ ⟨(201 : ℤ), (1552945009839167130104357311594983319435190611759664134261429 : ℤ), (1552951308068909199309257793444596497961015814205144832399512 : ℤ)⟩ = ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgA, mMgAa, mMgAb, mMgAc, mMgAd, mMgAe]
  exact mMgAf

theorem mdMgAa : dAdd ONE ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(199 : ℤ), (937508524286518765205136778845909225929342967944275135102741 : ℤ), (937508524286518765205136778845909225929342967944275135102788 : ℤ)⟩ := by rfl
theorem mdMgAb : dInv ⟨(199 : ℤ), (937508524286518765205136778845909225929342967944275135102741 : ℤ), (937508524286518765205136778845909225929342967944275135102788 : ℤ)⟩ = ⟨(200 : ℤ), (1377187412803581354803148946000007482317434635780830358027399 : ℤ), (1377187412803581354803148946000007482317434635780830358027469 : ℤ)⟩ := by rfl
theorem mdMgAc : dSub ⟨(200 : ℤ), (1377187412803581354803148946000007482317434635780830358027399 : ℤ), (1377187412803581354803148946000007482317434635780830358027469 : ℤ)⟩ ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ = ⟨(200 : ℤ), (-148407927877421797270546572717390994102538798584785194299397 : ℤ), (-148389051229529960159314464633906262193667332877580117078147 : ℤ)⟩ := by rfl
theorem mdMgAd : dMul (dInt 2) ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(201 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ := by rfl
theorem mdMgAe : dInv ⟨(201 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ = ⟨(198 : ℤ), (1204052647042564158386490734378486026990721114622037083239929 : ℤ), (1204052647042564158386490734378486026990721114622037083240342 : ℤ)⟩ := by rfl
theorem mdMgAf : dMul ⟨(200 : ℤ), (-148407927877421797270546572717390994102538798584785194299397 : ℤ), (-148389051229529960159314464633906262193667332877580117078147 : ℤ)⟩ ⟨(198 : ℤ), (1204052647042564158386490734378486026990721114622037083239929 : ℤ), (1204052647042564158386490734378486026990721114622037083240342 : ℤ)⟩ = ⟨(201 : ℤ), (-889597251325575240070981090584911087817308580068825253804521 : ℤ), (-889484099593595739996006950663412075699157446690777931964229 : ℤ)⟩ := by rfl

theorem md_MgA : dMatanD ⟨(202 : ℤ), (1072316017256189019473245861402623397345931768423029739616429 : ℤ), (1072316017256189019473245861402623397345931768423029739616796 : ℤ)⟩ ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ = ⟨(201 : ℤ), (-889597251325575240070981090584911087817308580068825253804521 : ℤ), (-889484099593595739996006950663412075699157446690777931964229 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgAa, mdMgAb, mdMgAc, mdMgAd, mdMgAe]
  exact mdMgAf

theorem PMgA_gates : (dLoBig JGA.value = true ∧
    dLoGt (dInv JGA.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGA.value)) ONE) = true ∧
    dLoBig (dInv JGA.value) = true ∧
    dLoBig (dAdd ONE JGA.value) = true ∧
    dLoBig (dMul (dInt 2) JGA.value) = true) := by
  rw [ev_GA, sqi_MgA]
  decide
theorem PMgA_hbig : dLoBig JGA.value = true := PMgA_gates.1
theorem PMgA_hR1 : dLoGt (dInv JGA.value) ONE = true :=
  PMgA_gates.2.1
theorem PMgA_hRden : dLoBig (dAdd (dSqrt (dInv JGA.value)) ONE) = true :=
  PMgA_gates.2.2.1
theorem PMgA_hRbig : dLoBig (dInv JGA.value) = true :=
  PMgA_gates.2.2.2.1
theorem PMgA_hden1 : dLoBig (dAdd ONE JGA.value) = true :=
  PMgA_gates.2.2.2.2.1
theorem PMgA_hden2 : dLoBig (dMul (dInt 2) JGA.value) = true :=
  PMgA_gates.2.2.2.2.2

def JMgA : DCJet := DCJetKit.matanMir JGA (DCJetKit.dMatanTight JGA.value)
theorem JMgA_mem : JetMem JMgA fMgA Dpt :=
  DCJetKit.matanMir_mem (JGA_mem) (DCJetKit.dMatanTight JGA.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGA_mem.2.1 x hx) PMgA_hbig PMgA_hR1 PMgA_hRden PMgA_hRbig)
    PMgA_hbig PMgA_hden1 PMgA_hden2

theorem ev_MgA : (JMgA).value = ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ := by
  rw [show (JMgA).value = dMatanMir (JGA).value (DCJetKit.dMatanTight (JGA).value) from rfl, ev_GA, mt_MgA]
  exact mv_MgA

/-- literal square root `dSqrt ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgB : dSqrt ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(201 : ℤ), (1351485579683195483258360997352687346442063423507380412769610 : ℤ), (1351485579683195483258360997352687346442063423507380412769841 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1351485579683195483258360997352687346442063423507380412769610 : ℤ)) (rhi := (1351485579683195483258360997352687346442063423507380412769840 : ℤ))
    (nlo := 1826513272091622927989977706541053673040663662701211478166410014324906721781525271221171613602131229678145005201215455232) (nhi := 1826513272091622927989977706541053673040663662701211478167031899348034951018160010550907643529307322236738946028477087744) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgB : dSqrt (dInv ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩) = ⟨(199 : ℤ), (1910675124400675513749799803156697807365313773498069152645998 : ℤ), (1910675124400675513749799803156697807365313773498069152646325 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩)) (K := (199 : ℤ))
    (rlo := (1910675124400675513749799803156697807365313773498069152645998 : ℤ)) (rhi := (1910675124400675513749799803156697807365313773498069152646324 : ℤ))
    (nlo := 3650679431003536849995865755061864360152915586472629712400187452232126571576443441746887140091653380983806588289648951296) (nhi := 3650679431003536849995865755061864360152915586472629712401434436154471548030264004330543882271210610506982035529842819072) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem u9_MgB : dMatanU9 (dInv ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩) = ⟨(201 : ℤ), (1584919889203151314954428093258176661084054899054499379083716 : ℤ), (1584928822750127366599654658266332196473771817135996149142261 : ℤ)⟩ := by
  unfold dMatanU9
  rw [sqi_MgB]
  rfl

theorem mt_MgB : DCJetKit.dMatanTight ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(201 : ℤ), (1584919889203151314954428093258176661084054899054499379083716 : ℤ), (1584928822750127366599654658266332196473771817135996149142261 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_neg (by decide)]
  exact u9_MgB

theorem mMgBa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgBb : dInv ⟨(201 : ℤ), (1351485579683195483258360997352687346442063423507380412769610 : ℤ), (1351485579683195483258360997352687346442063423507380412769841 : ℤ)⟩ = ⟨(198 : ℤ), (955337562200337756874899901578348903682656886749034576322999 : ℤ), (955337562200337756874899901578348903682656886749034576323163 : ℤ)⟩ := by rfl
theorem mMgBc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(198 : ℤ), (955337562200337756874899901578348903682656886749034576322999 : ℤ), (955337562200337756874899901578348903682656886749034576323163 : ℤ)⟩ = ⟨(198 : ℤ), (1500640733553204950051114872153145692654539645028575540010319 : ℤ), (1500640733553639387276727808387572444589991451715046101958236 : ℤ)⟩ := by rfl
theorem mMgBd : dInv ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(197 : ℤ), (1135911693685421478800341805225802583364279352210193201653398 : ℤ), (1135911693685421478800341805225802583364279352210193201653786 : ℤ)⟩ := by rfl
theorem mMgBe : dMul ⟨(201 : ℤ), (1584919889203151314954428093258176661084054899054499379083716 : ℤ), (1584928822750127366599654658266332196473771817135996149142261 : ℤ)⟩ ⟨(197 : ℤ), (1135911693685421478800341805225802583364279352210193201653398 : ℤ), (1135911693685421478800341805225802583364279352210193201653786 : ℤ)⟩ = ⟨(198 : ℤ), (1120347509434099287011260868495580185427808902054955489766452 : ℤ), (1120353824376055163432845431177033695109178538444434385300834 : ℤ)⟩ := by rfl
theorem mMgBf : dSub ⟨(198 : ℤ), (1500640733553204950051114872153145692654539645028575540010319 : ℤ), (1500640733553639387276727808387572444589991451715046101958236 : ℤ)⟩ ⟨(198 : ℤ), (1120347509434099287011260868495580185427808902054955489766452 : ℤ), (1120353824376055163432845431177033695109178538444434385300834 : ℤ)⟩ = ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ := by rfl

theorem mv_MgB : dMatanMir ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ ⟨(201 : ℤ), (1584919889203151314954428093258176661084054899054499379083716 : ℤ), (1584928822750127366599654658266332196473771817135996149142261 : ℤ)⟩ = ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgB, mMgBa, mMgBb, mMgBc, mMgBd, mMgBe]
  exact mMgBf

theorem mdMgBa : dAdd ONE ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(199 : ℤ), (945549272097524062544173204990140621033403726137497063385685 : ℤ), (945549272097524062544173204990140621033403726137497063385735 : ℤ)⟩ := by rfl
theorem mdMgBb : dInv ⟨(199 : ℤ), (945549272097524062544173204990140621033403726137497063385685 : ℤ), (945549272097524062544173204990140621033403726137497063385735 : ℤ)⟩ = ⟨(200 : ℤ), (1365476107003218672634125347289756138150370974442562278713738 : ℤ), (1365476107003218672634125347289756138150370974442562278713811 : ℤ)⟩ := by rfl
theorem mdMgBc : dSub ⟨(200 : ℤ), (1365476107003218672634125347289756138150370974442562278713738 : ℤ), (1365476107003218672634125347289756138150370974442562278713811 : ℤ)⟩ ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ = ⟨(200 : ℤ), (-155696789474941728427742412278212898498359224197800170053398 : ℤ), (-155671529705380473838952416614691852031073451894002340124129 : ℤ)⟩ := by rfl
theorem mdMgBd : dMul (dInt 2) ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(201 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ := by rfl
theorem mdMgBe : dInv ⟨(201 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ = ⟨(198 : ℤ), (1135911693685421478800341805225802583364279352210193201653398 : ℤ), (1135911693685421478800341805225802583364279352210193201653786 : ℤ)⟩ := by rfl
theorem mdMgBf : dMul ⟨(200 : ℤ), (-155696789474941728427742412278212898498359224197800170053398 : ℤ), (-155671529705380473838952416614691852031073451894002340124129 : ℤ)⟩ ⟨(198 : ℤ), (1135911693685421478800341805225802583364279352210193201653398 : ℤ), (1135911693685421478800341805225802583364279352210193201653786 : ℤ)⟩ = ⟨(201 : ℤ), (-880471052213681405372914724582720953059755355066614219457910 : ℤ), (-880328207290807434383544427400581189182008195706663814140873 : ℤ)⟩ := by rfl

theorem md_MgB : dMatanD ⟨(202 : ℤ), (1136641999744231398185537270556474558178417833968805165879982 : ℤ), (1136641999744231398185537270556474558178417833968805165880369 : ℤ)⟩ ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ = ⟨(201 : ℤ), (-880471052213681405372914724582720953059755355066614219457910 : ℤ), (-880328207290807434383544427400581189182008195706663814140873 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgBa, mdMgBb, mdMgBc, mdMgBd, mdMgBe]
  exact mdMgBf

theorem PMgB_gates : (dLoBig JGB.value = true ∧
    dLoGt (dInv JGB.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGB.value)) ONE) = true ∧
    dLoBig (dInv JGB.value) = true ∧
    dLoBig (dAdd ONE JGB.value) = true ∧
    dLoBig (dMul (dInt 2) JGB.value) = true) := by
  rw [ev_GB, sqi_MgB]
  decide
theorem PMgB_hbig : dLoBig JGB.value = true := PMgB_gates.1
theorem PMgB_hR1 : dLoGt (dInv JGB.value) ONE = true :=
  PMgB_gates.2.1
theorem PMgB_hRden : dLoBig (dAdd (dSqrt (dInv JGB.value)) ONE) = true :=
  PMgB_gates.2.2.1
theorem PMgB_hRbig : dLoBig (dInv JGB.value) = true :=
  PMgB_gates.2.2.2.1
theorem PMgB_hden1 : dLoBig (dAdd ONE JGB.value) = true :=
  PMgB_gates.2.2.2.2.1
theorem PMgB_hden2 : dLoBig (dMul (dInt 2) JGB.value) = true :=
  PMgB_gates.2.2.2.2.2

def JMgB : DCJet := DCJetKit.matanMir JGB (DCJetKit.dMatanTight JGB.value)
theorem JMgB_mem : JetMem JMgB fMgB Dpt :=
  DCJetKit.matanMir_mem (JGB_mem) (DCJetKit.dMatanTight JGB.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGB_mem.2.1 x hx) PMgB_hbig PMgB_hR1 PMgB_hRden PMgB_hRbig)
    PMgB_hbig PMgB_hden1 PMgB_hden2

theorem ev_MgB : (JMgB).value = ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ := by
  rw [show (JMgB).value = dMatanMir (JGB).value (DCJetKit.dMatanTight (JGB).value) from rfl, ev_GB, mt_MgB]
  exact mv_MgB

/-- literal square root `dSqrt ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩` — `Nat.sqrt` never reaches the kernel. -/
theorem sq_MgC : dSqrt ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(201 : ℤ), (1780628042877404742827779855406470728726237347374028663051610 : ℤ), (1780628042877404742827779855406470728726237347374028663051920 : ℤ)⟩ := by
  refine dSqrt_val (A := ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩) (K := (201 : ℤ))
    (rlo := (1780628042877404742827779855406470728726237347374028663051610 : ℤ)) (rhi := (1780628042877404742827779855406470728726237347374028663051919 : ℤ))
    (nlo := 3170636227081416743295725457015616681260869322517731123628599309549328617936037356224830877412460907217289416471893508096) (nhi := 3170636227081416743295725457015616681260869322517731123629698455171601767284508058295992232632586094065036846771239649280) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

/-- literal square root `dSqrt (dInv ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩)` — `Nat.sqrt` never reaches the kernel. -/
theorem sqi_MgC : dSqrt (dInv ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩) = ⟨(199 : ℤ), (1450190503522635506074632845368698855243138285841559965372689 : ℤ), (1450190503522635506074632845368698855243138285841559965372942 : ℤ)⟩ := by
  refine dSqrt_val (A := (dInv ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩)) (K := (199 : ℤ))
    (rlo := (1450190503522635506074632845368698855243138285841559965372689 : ℤ)) (rhi := (1450190503522635506074632845368698855243138285841559965372941 : ℤ))
    (nlo := 2103052496507235104153210595340996812493691223237324025240536250735856193992302595671902989202745464541415327829634056192) (nhi := 2103052496507235104153210595340996812493691223237324025241265800607949775577398646461825877024290544700592715776860880896) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

theorem wp_MgC : dMatanWp (dInv ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩) = ⟨(200 : ℤ), (948053038354912661384296879001339533923274682278776898456010 : ℤ), (948073420413619239655883567793444754252288767077366845862001 : ℤ)⟩ := by
  unfold dMatanWp
  rw [sqi_MgC]
  rfl

theorem mt_MgC : DCJetKit.dMatanTight ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(200 : ℤ), (948053038354912661384296879001339533923274682278776898456010 : ℤ), (948073420413619239655883567793444754252288767077366845862001 : ℤ)⟩ := by
  unfold DCJetKit.dMatanTight
  rw [if_pos (by decide)]
  exact wp_MgC

theorem mMgCa : dMul HALF PIbr = ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ := by rfl
theorem mMgCb : dInv ⟨(201 : ℤ), (1780628042877404742827779855406470728726237347374028663051610 : ℤ), (1780628042877404742827779855406470728726237347374028663051920 : ℤ)⟩ = ⟨(199 : ℤ), (1450190503522635506074632845368698855243138285841559965372689 : ℤ), (1450190503522635506074632845368698855243138285841559965372942 : ℤ)⟩ := by rfl
theorem mMgCc : dMul ⟨(199 : ℤ), (1262086188654265777421153155602991849900774548621528932548608 : ℤ), (1262086188654631152830485881332542771108953619376442915684352 : ℤ)⟩ ⟨(199 : ℤ), (1450190503522635506074632845368698855243138285841559965372689 : ℤ), (1450190503522635506074632845368698855243138285841559965372942 : ℤ)⟩ = ⟨(198 : ℤ), (1138976958042888726686790250723831823017841659328209624539405 : ℤ), (1138976958043218461831669063728046374466210911352386941402757 : ℤ)⟩ := by rfl
theorem mMgCd : dInv ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(198 : ℤ), (1308732781590853941123194192680534961484630657897313245707817 : ℤ), (1308732781590853941123194192680534961484630657897313245708271 : ℤ)⟩ := by rfl
theorem mMgCe : dMul ⟨(200 : ℤ), (948053038354912661384296879001339533923274682278776898456010 : ℤ), (948073420413619239655883567793444754252288767077366845862001 : ℤ)⟩ ⟨(198 : ℤ), (1308732781590853941123194192680534961484630657897313245707817 : ℤ), (1308732781590853941123194192680534961484630657897313245708271 : ℤ)⟩ = ⟨(199 : ℤ), (1544238863986860668298571083202409722050464691673291939844947 : ℤ), (1544272063360639772263330251263466256524308252800736810529338 : ℤ)⟩ := by rfl
theorem mMgCf : dSub ⟨(198 : ℤ), (1138976958042888726686790250723831823017841659328209624539405 : ℤ), (1138976958043218461831669063728046374466210911352386941402757 : ℤ)⟩ ⟨(199 : ℤ), (1544238863986860668298571083202409722050464691673291939844947 : ℤ), (1544272063360639772263330251263466256524308252800736810529338 : ℤ)⟩ = ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ := by rfl

theorem mv_MgC : dMatanMir ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ ⟨(200 : ℤ), (948053038354912661384296879001339533923274682278776898456010 : ℤ), (948073420413619239655883567793444754252288767077366845862001 : ℤ)⟩ = ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ := by
  unfold dMatanMir dDiv
  rw [sq_MgC, mMgCa, mMgCb, mMgCc, mMgCd, mMgCe]
  exact mMgCf

theorem mdMgCa : dAdd ONE ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(199 : ℤ), (1050105493150340945391663451146100284970867597416991991781293 : ℤ), (1050105493150340945391663451146100284970867597416991991781380 : ℤ)⟩ := by rfl
theorem mdMgCb : dInv ⟨(199 : ℤ), (1050105493150340945391663451146100284970867597416991991781293 : ℤ), (1050105493150340945391663451146100284970867597416991991781380 : ℤ)⟩ = ⟨(200 : ℤ), (1229519269697418110205411641278583987359557531499916360663537 : ℤ), (1229519269697418110205411641278583987359557531499916360663640 : ℤ)⟩ := by rfl
theorem mdMgCc : dSub ⟨(200 : ℤ), (1229519269697418110205411641278583987359557531499916360663537 : ℤ), (1229519269697418110205411641278583987359557531499916360663640 : ℤ)⟩ ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ = ⟨(200 : ℤ), (-237910834501734400524122447228782066404356730563047525257597 : ℤ), (-237844435752857252015088859089810791663192600211448516435304 : ℤ)⟩ := by rfl
theorem mdMgCd : dMul (dInt 2) ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(200 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ := by rfl
theorem mdMgCe : dInv ⟨(200 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ = ⟨(199 : ℤ), (1308732781590853941123194192680534961484630657897313245707817 : ℤ), (1308732781590853941123194192680534961484630657897313245708271 : ℤ)⟩ := by rfl
theorem mdMgCf : dMul ⟨(200 : ℤ), (-237910834501734400524122447228782066404356730563047525257597 : ℤ), (-237844435752857252015088859089810791663192600211448516435304 : ℤ)⟩ ⟨(199 : ℤ), (1308732781590853941123194192680534961484630657897313245707817 : ℤ), (1308732781590853941123194192680534961484630657897313245708271 : ℤ)⟩ = ⟨(202 : ℤ), (-1550086933695741092373209202832071891044462702536852443552267 : ℤ), (-1549654318538622376385206776998392878209713234937207933619496 : ℤ)⟩ := by rfl

theorem md_MgC : dMatanD ⟨(201 : ℤ), (986545884083383230482729619902075934839064402102382296522423 : ℤ), (986545884083383230482729619902075934839064402102382296522765 : ℤ)⟩ ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ = ⟨(202 : ℤ), (-1550086933695741092373209202832071891044462702536852443552267 : ℤ), (-1549654318538622376385206776998392878209713234937207933619496 : ℤ)⟩ := by
  unfold dMatanD dDiv
  rw [mdMgCa, mdMgCb, mdMgCc, mdMgCd, mdMgCe]
  exact mdMgCf

theorem PMgC_gates : (dLoBig JGC.value = true ∧
    dLoGt (dInv JGC.value) ONE = true ∧
    dLoBig (dAdd (dSqrt (dInv JGC.value)) ONE) = true ∧
    dLoBig (dInv JGC.value) = true ∧
    dLoBig (dAdd ONE JGC.value) = true ∧
    dLoBig (dMul (dInt 2) JGC.value) = true) := by
  rw [ev_GC, sqi_MgC]
  decide
theorem PMgC_hbig : dLoBig JGC.value = true := PMgC_gates.1
theorem PMgC_hR1 : dLoGt (dInv JGC.value) ONE = true :=
  PMgC_gates.2.1
theorem PMgC_hRden : dLoBig (dAdd (dSqrt (dInv JGC.value)) ONE) = true :=
  PMgC_gates.2.2.1
theorem PMgC_hRbig : dLoBig (dInv JGC.value) = true :=
  PMgC_gates.2.2.2.1
theorem PMgC_hden1 : dLoBig (dAdd ONE JGC.value) = true :=
  PMgC_gates.2.2.2.2.1
theorem PMgC_hden2 : dLoBig (dMul (dInt 2) JGC.value) = true :=
  PMgC_gates.2.2.2.2.2

def JMgC : DCJet := DCJetKit.matanMir JGC (DCJetKit.dMatanTight JGC.value)
theorem JMgC_mem : JetMem JMgC fMgC Dpt :=
  DCJetKit.matanMir_mem (JGC_mem) (DCJetKit.dMatanTight JGC.value)
    (fun x hx => DCJetKit.dMatanTight_mem (JGC_mem.2.1 x hx) PMgC_hbig PMgC_hR1 PMgC_hRden PMgC_hRbig)
    PMgC_hbig PMgC_hden1 PMgC_hden2

theorem ev_MgC : (JMgC).value = ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ := by
  rw [show (JMgC).value = dMatanMir (JGC).value (DCJetKit.dMatanTight (JGC).value) from rfl, ev_GC, mt_MgC]
  exact mv_MgC

def JDihA : DCJet := DCJetKit.mul JWA JMgA
theorem JDihA_mem : JetMem JDihA fDihA Dpt :=
  DCJetKit.mul_mem (JWA_mem) (JMgA_mem)

theorem op_DihA : dMul ⟨(202 : ℤ), (862298009076941905488898486797240865218360403741950246774509 : ℤ), (862298009076941905488898486797240865218360403741950246774516 : ℤ)⟩ ⟨(198 : ℤ), (381394116008277828740615852658478436127775492164602618776404 : ℤ), (381398835170250788018423879679349619104993358591403888081699 : ℤ)⟩ = ⟨(202 : ℤ), (818638622895391052529127859313897281207781911617814440628431 : ℤ), (818648752281494848190541490219856118000345517071545375186401 : ℤ)⟩ := by
  rfl

theorem ev_DihA : (JDihA).value = ⟨(202 : ℤ), (818638622895391052529127859313897281207781911617814440628431 : ℤ), (818648752281494848190541490219856118000345517071545375186401 : ℤ)⟩ := by
  rw [show (JDihA).value = dMul (JWA).value (JMgA).value from rfl, ev_WA, ev_MgA]
  exact op_DihA

def JDihB : DCJet := DCJetKit.mul JWB JMgB
theorem JDihB_mem : JetMem JDihB fDihB Dpt :=
  DCJetKit.mul_mem (JWB_mem) (JMgB_mem)

theorem op_DihB : dMul ⟨(202 : ℤ), (887785068781979153106968947565936126465625777824364717987848 : ℤ), (887785068781979153106968947565936126465625777824364717987854 : ℤ)⟩ ⟨(198 : ℤ), (380286909177149786618269440976111997545361106584141154709485 : ℤ), (380293224119540100265466939891992259162182549660090612191784 : ℤ)⟩ = ⟨(202 : ℤ), (840388441923798461021609967020578807475171992599592979725818 : ℤ), (840402397188805393093817487023057601956518465966233326072344 : ℤ)⟩ := by
  rfl

theorem ev_DihB : (JDihB).value = ⟨(202 : ℤ), (840388441923798461021609967020578807475171992599592979725818 : ℤ), (840402397188805393093817487023057601956518465966233326072344 : ℤ)⟩ := by
  rw [show (JDihB).value = dMul (JWB).value (JMgB).value from rfl, ev_WB, ev_MgB]
  exact op_DihB

def JDihC : DCJet := DCJetKit.mul JWC JMgC
theorem JDihC_mem : JetMem JDihC fDihC Dpt :=
  DCJetKit.mul_mem (JWC_mem) (JMgC_mem)

theorem op_DihC : dMul ⟨(202 : ℤ), (1169686908454916544514486923722952161952012388506325351528758 : ℤ), (1169686908454916544514486923722952161952012388506325351528769 : ℤ)⟩ ⟨(199 : ℤ), (733681852725137681110250250184197389511375065855682438549472 : ℤ), (733715052099576255364767044253683026881957131031481942960567 : ℤ)⟩ = ⟨(202 : ℤ), (1068091033340709289713524634207837187217760244463988752805618 : ℤ), (1068139364853910348016968648803866936478263526705998147802507 : ℤ)⟩ := by
  rfl

theorem ev_DihC : (JDihC).value = ⟨(202 : ℤ), (1068091033340709289713524634207837187217760244463988752805618 : ℤ), (1068139364853910348016968648803866936478263526705998147802507 : ℤ)⟩ := by
  rw [show (JDihC).value = dMul (JWC).value (JMgC).value from rfl, ev_WC, ev_MgC]
  exact op_DihC

def JSeA : DCJet := DCJetKit.mul JMtA JIA
theorem JSeA_mem : JetMem JSeA fSeA Dpt :=
  DCJetKit.mul_mem (JMtA_mem) (JIA_mem)

theorem op_SeA : dMul ⟨(200 : ℤ), (1605182242761259241746093515178406056464391573641090454600878 : ℤ), (1605182242761315071727396218558088168198853459004420340546532 : ℤ)⟩ ⟨(204 : ℤ), (967924847100076862763948394385695756474911542319661092148748 : ℤ), (967924847100076863045414380170159443577058772719079183650758 : ℤ)⟩ = ⟨(204 : ℤ), (966867255675005411194682408483391891556652523292488247362597 : ℤ), (966867255675039040168813231951590051324341859653539124907620 : ℤ)⟩ := by
  rfl

theorem ev_SeA : (JSeA).value = ⟨(204 : ℤ), (966867255675005411194682408483391891556652523292488247362597 : ℤ), (966867255675039040168813231951590051324341859653539124907620 : ℤ)⟩ := by
  rw [show (JSeA).value = dMul (JMtA).value (JIA).value from rfl, ev_MtA, ev_IA]
  exact op_SeA

def JSeB : DCJet := DCJetKit.mul JMtB JIB
theorem JSeB_mem : JetMem JSeB fSeB Dpt :=
  DCJetKit.mul_mem (JMtB_mem) (JIB_mem)

theorem op_SeB : dMul ⟨(200 : ℤ), (1604608057110327246095012691423460250813592981886360387245682 : ℤ), (1604608057110557738508792275723676423463570473706786127157132 : ℤ)⟩ ⟨(204 : ℤ), (1115374097162234065383872961265915749158488237767651560879466 : ℤ), (1115374097162234065700152030743822374104406456533700622276905 : ℤ)⟩ = ⟨(204 : ℤ), (1113756855401343385627943096692582944240018807220977174205482 : ℤ), (1113756855401503370498762831028973637464047571293436979190513 : ℤ)⟩ := by
  rfl

theorem ev_SeB : (JSeB).value = ⟨(204 : ℤ), (1113756855401343385627943096692582944240018807220977174205482 : ℤ), (1113756855401503370498762831028973637464047571293436979190513 : ℤ)⟩ := by
  rw [show (JSeB).value = dMul (JMtB).value (JIB).value from rfl, ev_MtB, ev_IB]
  exact op_SeB

def JSeC : DCJet := DCJetKit.mul JMtC JIC
theorem JSeC_mem : JetMem JSeC fSeC Dpt :=
  DCJetKit.mul_mem (JMtC_mem) (JIC_mem)

theorem op_SeC : dMul ⟨(200 : ℤ), (1605251733199857052774616656595705386110349385239744270371750 : ℤ), (1605251733199902657476537645125142932294344243029767474757772 : ℤ)⟩ ⟨(204 : ℤ), (948540442223145994352916239637870076727879857974802803369000 : ℤ), (948540442223145994629382685007595316690136029017825511694095 : ℤ)⟩ = ⟨(204 : ℤ), (947545049623244232480770335185703708533393691581844399229826 : ℤ), (947545049623271152216774082363693518052261703406315852914013 : ℤ)⟩ := by
  rfl

theorem ev_SeC : (JSeC).value = ⟨(204 : ℤ), (947545049623244232480770335185703708533393691581844399229826 : ℤ), (947545049623271152216774082363693518052261703406315852914013 : ℤ)⟩ := by
  rw [show (JSeC).value = dMul (JMtC).value (JIC).value from rfl, ev_MtC, ev_IC]
  exact op_SeC

def JSe1 : DCJet := DCJetKit.add JSeA JSeB
theorem JSe1_mem : JetMem JSe1 fSe1 Dpt :=
  DCJetKit.add_mem (JSeA_mem) (JSeB_mem)

theorem op_Se1 : dAdd ⟨(204 : ℤ), (966867255675005411194682408483391891556652523292488247362597 : ℤ), (966867255675039040168813231951590051324341859653539124907620 : ℤ)⟩ ⟨(204 : ℤ), (1113756855401343385627943096692582944240018807220977174205482 : ℤ), (1113756855401503370498762831028973637464047571293436979190513 : ℤ)⟩ = ⟨(203 : ℤ), (1040312055538174398411312752587987417898335665256732710784039 : ℤ), (1040312055538271205333788031490281844394194715473488052049067 : ℤ)⟩ := by
  rfl

theorem ev_Se1 : (JSe1).value = ⟨(203 : ℤ), (1040312055538174398411312752587987417898335665256732710784039 : ℤ), (1040312055538271205333788031490281844394194715473488052049067 : ℤ)⟩ := by
  rw [show (JSe1).value = dAdd (JSeA).value (JSeB).value from rfl, ev_SeA, ev_SeB]
  exact op_Se1

def JSe : DCJet := DCJetKit.add JSe1 JSeC
theorem JSe_mem : JetMem JSe fSe Dpt :=
  DCJetKit.add_mem (JSe1_mem) (JSeC_mem)

theorem op_Se : dAdd ⟨(203 : ℤ), (1040312055538174398411312752587987417898335665256732710784039 : ℤ), (1040312055538271205333788031490281844394194715473488052049067 : ℤ)⟩ ⟨(204 : ℤ), (947545049623244232480770335185703708533393691581844399229826 : ℤ), (947545049623271152216774082363693518052261703406315852914013 : ℤ)⟩ = ⟨(203 : ℤ), (1514084580349796514651697920180839272165032511047654910398952 : ℤ), (1514084580349906781442175072672128603420325567176645978506074 : ℤ)⟩ := by
  rfl

theorem ev_Se : (JSe).value = ⟨(203 : ℤ), (1514084580349796514651697920180839272165032511047654910398952 : ℤ), (1514084580349906781442175072672128603420325567176645978506074 : ℤ)⟩ := by
  rw [show (JSe).value = dAdd (JSe1).value (JSeC).value from rfl, ev_Se1, ev_SeC]
  exact op_Se

def JK1Se : DCJet := DCJetKit.mul JK1 JSe
theorem JK1Se_mem : JetMem JK1Se fK1Se Dpt :=
  DCJetKit.mul_mem (JK1_mem) (JSe_mem)

theorem op_K1Se : dMul ⟨(200 : ℤ), (1035367293417576623206012836180143096644245248062714744199711 : ℤ), (1035367395718729557748648279712693635552429475650930963275090 : ℤ)⟩ ⟨(203 : ℤ), (1514084580349796514651697920180839272165032511047654910398952 : ℤ), (1514084580349906781442175072672128603420325567176645978506074 : ℤ)⟩ = ⟨(203 : ℤ), (975540817869516163850351477024309848218596970024574496873103 : ℤ), (975540914259487718891191445232188507781927507234952739561007 : ℤ)⟩ := by
  rfl

theorem ev_K1Se : (JK1Se).value = ⟨(203 : ℤ), (975540817869516163850351477024309848218596970024574496873103 : ℤ), (975540914259487718891191445232188507781927507234952739561007 : ℤ)⟩ := by
  rw [show (JK1Se).value = dMul (JK1).value (JSe).value from rfl, ev_K1, ev_Se]
  exact op_K1Se

def JFirst : DCJet := DCJetKit.sub JC112 JK1Se
theorem JFirst_mem : JetMem JFirst fFirst Dpt :=
  DCJetKit.sub_mem (JC112_mem Dpt) (JK1Se_mem)

theorem op_First : dAdd ⟨(203 : ℤ), (1071292029505993517027974728227441735014801995855195223534250 : ℤ), (1071292029505993517027974728227441735014801995855195223534251 : ℤ)⟩ (dNeg ⟨(203 : ℤ), (975540817869516163850351477024309848218596970024574496873103 : ℤ), (975540914259487718891191445232188507781927507234952739561007 : ℤ)⟩) = ⟨(203 : ℤ), (95751115246505798136783282995253227232874488620242483973243 : ℤ), (95751211636477353177623251203131886796205025830620726661148 : ℤ)⟩ := by
  rfl

theorem ev_First : (JFirst).value = ⟨(203 : ℤ), (95751115246505798136783282995253227232874488620242483973243 : ℤ), (95751211636477353177623251203131886796205025830620726661148 : ℤ)⟩ := by
  rw [show (JFirst).value = dAdd (JC112).value (dNeg (JK1Se).value) from rfl, ev_C112, ev_K1Se]
  exact op_First

def JLf5DihA : DCJet := DCJetKit.mul JLf5 JDihA
theorem JLf5DihA_mem : JetMem JLf5DihA fLf5DihA Dpt :=
  DCJetKit.mul_mem (JLf5_mem) (JDihA_mem)

theorem op_Lf5DihA : dMul ⟨(201 : ℤ), (1359516800445701234177680561917978686903585030606511985323245 : ℤ), (1359516800445701234177680561917978686903585030606511985323294 : ℤ)⟩ ⟨(202 : ℤ), (818638622895391052529127859313897281207781911617814440628431 : ℤ), (818648752281494848190541490219856118000345517071545375186401 : ℤ)⟩ = ⟨(204 : ℤ), (1385184656367053246688238630888233720482069986467643332570812 : ℤ), (1385201795883583470726288050010963425352369354739714472637944 : ℤ)⟩ := by
  rfl

theorem ev_Lf5DihA : (JLf5DihA).value = ⟨(204 : ℤ), (1385184656367053246688238630888233720482069986467643332570812 : ℤ), (1385201795883583470726288050010963425352369354739714472637944 : ℤ)⟩ := by
  rw [show (JLf5DihA).value = dMul (JLf5).value (JDihA).value from rfl, ev_Lf5, ev_DihA]
  exact op_Lf5DihA

def JLf6DihB : DCJet := DCJetKit.mul JLf6 JDihB
theorem JLf6DihB_mem : JetMem JLf6DihB fLf6DihB Dpt :=
  DCJetKit.mul_mem (JLf6_mem) (JDihB_mem)

theorem op_Lf6DihB : dMul ⟨(201 : ℤ), (1184011100171166911643582977590070532271563638926436072849660 : ℤ), (1184011100171166911643582977590070532271563638926436072849709 : ℤ)⟩ ⟨(202 : ℤ), (840388441923798461021609967020578807475171992599592979725818 : ℤ), (840402397188805393093817487023057601956518465966233326072344 : ℤ)⟩ = ⟨(204 : ℤ), (1238416437084441220758683487686997673054692665818170038140673 : ℤ), (1238437001895552724678001974009307306754693278117441499052940 : ℤ)⟩ := by
  rfl

theorem ev_Lf6DihB : (JLf6DihB).value = ⟨(204 : ℤ), (1238416437084441220758683487686997673054692665818170038140673 : ℤ), (1238437001895552724678001974009307306754693278117441499052940 : ℤ)⟩ := by
  rw [show (JLf6DihB).value = dMul (JLf6).value (JDihB).value from rfl, ev_Lf6, ev_DihB]
  exact op_Lf6DihB

def JPosA : DCJet := DCJetKit.add JLf5DihA JLf6DihB
theorem JPosA_mem : JetMem JPosA fPosA Dpt :=
  DCJetKit.add_mem (JLf5DihA_mem) (JLf6DihB_mem)

theorem op_PosA : dAdd ⟨(204 : ℤ), (1385184656367053246688238630888233720482069986467643332570812 : ℤ), (1385201795883583470726288050010963425352369354739714472637944 : ℤ)⟩ ⟨(204 : ℤ), (1238416437084441220758683487686997673054692665818170038140673 : ℤ), (1238437001895552724678001974009307306754693278117441499052940 : ℤ)⟩ = ⟨(203 : ℤ), (1311800546725747233723461059287615696768381326142906685355742 : ℤ), (1311819398889568097702145012010135366053531316428577985845442 : ℤ)⟩ := by
  rfl

theorem ev_PosA : (JPosA).value = ⟨(203 : ℤ), (1311800546725747233723461059287615696768381326142906685355742 : ℤ), (1311819398889568097702145012010135366053531316428577985845442 : ℤ)⟩ := by
  rw [show (JPosA).value = dAdd (JLf5DihA).value (JLf6DihB).value from rfl, ev_Lf5DihA, ev_Lf6DihB]
  exact op_PosA

def JPos : DCJet := DCJetKit.mul JK2 JPosA
theorem JPos_mem : JetMem JPos fPos Dpt :=
  DCJetKit.mul_mem (JK2_mem) (JPosA_mem)

theorem op_Pos : dMul ⟨(203 : ℤ), (831976010723602339748975401176672747224614346424194237976669 : ℤ), (831976338086573420214090764996862982876047143922201206657370 : ℤ)⟩ ⟨(203 : ℤ), (1311800546725747233723461059287615696768381326142906685355742 : ℤ), (1311819398889568097702145012010135366053531316428577985845442 : ℤ)⟩ = ⟨(207 : ℤ), (1358343079410009747044187282060931210929611868454917309161837 : ℤ), (1358363134930137235698079614836237029178568791613279631314403 : ℤ)⟩ := by
  rfl

theorem ev_Pos : (JPos).value = ⟨(207 : ℤ), (1358343079410009747044187282060931210929611868454917309161837 : ℤ), (1358363134930137235698079614836237029178568791613279631314403 : ℤ)⟩ := by
  rw [show (JPos).value = dMul (JK2).value (JPosA).value from rfl, ev_K2, ev_PosA]
  exact op_Pos

def JNeg2 : DCJet := DCJetKit.mul JC008 JDihC
theorem JNeg2_mem : JetMem JNeg2 fNeg2 Dpt :=
  DCJetKit.mul_mem (JC008_mem Dpt) (JDihC_mem)

theorem op_Neg2 : dMul ⟨(206 : ℤ), (822752278660603021077484591278675252491367932816789931674304 : ℤ), (822752278660603021077484591278675252491367932816789931674305 : ℤ)⟩ ⟨(202 : ℤ), (1068091033340709289713524634207837187217760244463988752805618 : ℤ), (1068139364853910348016968648803866936478263526705998147802507 : ℤ)⟩ = ⟨(209 : ℤ), (1093725218140886312666649225428825279710986490331124482872952 : ℤ), (1093774709610404196369375896375159742953741851346942103349768 : ℤ)⟩ := by
  rfl

theorem ev_Neg2 : (JNeg2).value = ⟨(209 : ℤ), (1093725218140886312666649225428825279710986490331124482872952 : ℤ), (1093774709610404196369375896375159742953741851346942103349768 : ℤ)⟩ := by
  rw [show (JNeg2).value = dMul (JC008).value (JDihC).value from rfl, ev_C008, ev_DihC]
  exact op_Neg2

def JFirstPos : DCJet := DCJetKit.add JFirst JPos
theorem JFirstPos_mem : JetMem JFirstPos fFirstPos Dpt :=
  DCJetKit.add_mem (JFirst_mem) (JPos_mem)

theorem op_FirstPos : dAdd ⟨(203 : ℤ), (95751115246505798136783282995253227232874488620242483973243 : ℤ), (95751211636477353177623251203131886796205025830620726661148 : ℤ)⟩ ⟨(207 : ℤ), (1358343079410009747044187282060931210929611868454917309161837 : ℤ), (1358363134930137235698079614836237029178568791613279631314403 : ℤ)⟩ = ⟨(206 : ℤ), (1445180461677051258616359904992491423327801843189398526366862 : ℤ), (1445191260556887443270025817043173608958924602451605628946386 : ℤ)⟩ := by
  rfl

theorem ev_FirstPos : (JFirstPos).value = ⟨(206 : ℤ), (1445180461677051258616359904992491423327801843189398526366862 : ℤ), (1445191260556887443270025817043173608958924602451605628946386 : ℤ)⟩ := by
  rw [show (JFirstPos).value = dAdd (JFirst).value (JPos).value from rfl, ev_First, ev_Pos]
  exact op_FirstPos

def JTop : DCJet := DCJetKit.sub JFirstPos JNeg2
theorem JTop_mem : JetMem JTop fTop Dpt :=
  DCJetKit.sub_mem (JFirstPos_mem) (JNeg2_mem)

theorem op_Top : dAdd ⟨(206 : ℤ), (1445180461677051258616359904992491423327801843189398526366862 : ℤ), (1445191260556887443270025817043173608958924602451605628946386 : ℤ)⟩ (dNeg ⟨(209 : ℤ), (1093725218140886312666649225428825279710986490331124482872952 : ℤ), (1093774709610404196369375896375159742953741851346942103349768 : ℤ)⟩) = ⟨(206 : ℤ), (1308458622975750734070187917945596455458584111771030763448141 : ℤ), (1308475608289276654186694663864570448995051291160215068587267 : ℤ)⟩ := by
  rfl

theorem ev_Top : (JTop).value = ⟨(206 : ℤ), (1308458622975750734070187917945596455458584111771030763448141 : ℤ), (1308475608289276654186694663864570448995051291160215068587267 : ℤ)⟩ := by
  rw [show (JTop).value = dAdd (JFirstPos).value (dNeg (JNeg2).value) from rfl, ev_FirstPos, ev_Neg2]
  exact op_Top

end Pt


/-! ## 5. The T2 terminal

`V` and `G` are the **literal** brackets of `Pt.JTop.value` / `Box.JTop.part i`
(proved equal to the tree slots in `V_mem`/`G_mem`), so the slack below is one
pure-integer kernel computation: `Nat.sqrt` inside the tree never reaches it. -/

def V : DC := ⟨(206 : ℤ), (1308458622975750734070187917945596455458584111771030763448141 : ℤ), (1308475608289276654186694663864570448995051291160215068587267 : ℤ)⟩

def G : Fin 3 → DC
  | 0 => ⟨(202 : ℤ), (-1544162837406141969854297422165889914141135232883190192826690 : ℤ), (1427369865047678715022766238508162840028740916433377212433855 : ℤ)⟩
  | 1 => ⟨(202 : ℤ), (-1398780690382285921282414027748183517492716603617961966497140 : ℤ), (1430585333007238820342294029553497604837419845569885327288397 : ℤ)⟩
  | 2 => ⟨(202 : ℤ), (-1441715426504463452801533752295543302274465472262201672319738 : ℤ), (1460133975467686322341022359054718578583615595567664935032957 : ℤ)⟩

theorem V_mem : V.mem (fTop c) := by
  have h := Pt.JTop_mem.2.1 c (show c ∈ Dpt from rfl)
  rwa [Pt.ev_Top] at h

theorem G0_eq : G 0 = Box.JTop.part 0 := by
  rw [show G 0 = ⟨(202 : ℤ), (-1544162837406141969854297422165889914141135232883190192826690 : ℤ), (1427369865047678715022766238508162840028740916433377212433855 : ℤ)⟩ from rfl]
  exact Box.p0_Top.symm

theorem G1_eq : G 1 = Box.JTop.part 1 := by
  rw [show G 1 = ⟨(202 : ℤ), (-1398780690382285921282414027748183517492716603617961966497140 : ℤ), (1430585333007238820342294029553497604837419845569885327288397 : ℤ)⟩ from rfl]
  exact Box.p1_Top.symm

theorem G2_eq : G 2 = Box.JTop.part 2 := by
  rw [show G 2 = ⟨(202 : ℤ), (-1441715426504463452801533752295543302274465472262201672319738 : ℤ), (1460133975467686322341022359054718578583615595567664935032957 : ℤ)⟩ from rfl]
  exact Box.p2_Top.symm

theorem G_mem : ∀ x ∈ D, ∀ i, (G i).mem (partial1 i fTop x) := by
  intro x hx i
  rw [show G i = Box.JTop.part i from by
    fin_cases i
    · exact G0_eq
    · exact G1_eq
    · exact G2_eq]
  exact Box.JTop_mem.2.2 x hx i

/-- Scale of the integer slack: far above every `DC.k` in the tree. -/
def KZ : ℤ := 1024

/-- **The T2 slack, scaled by `2^KZ` and evaluated in `ℤ`.**  A `ℚ`
version is unusable for `decide`: `Rat.blt` does not reduce in the kernel
(measured: even `0 < (1/3 : ℚ)` is stuck), so the sign is decided on the
integer scale `2^KZ` and transported to `ℝ` by `dcSlack` below. -/
def slackZ : ℤ :=
  V.lo * (2 : ℤ) ^ (KZ - V.k).toNat -
    (wz0 * ((dAbs (G 0)).hi * (2 : ℤ) ^ (KZ - 201 - (G 0).k).toNat) +
     wz1 * ((dAbs (G 1)).hi * (2 : ℤ) ^ (KZ - 201 - (G 1).k).toNat) +
     wz2 * ((dAbs (G 2)).hi * (2 : ℤ) ^ (KZ - 201 - (G 2).k).toNat))

/-- The `k` bounds (needed by the cast bridge) and the slack sign, in **one**
kernel computation on literals. -/
theorem val_facts :
    ((V.k ≤ KZ ∧ (G 0).k ≤ KZ - 201 ∧ (G 1).k ≤ KZ - 201 ∧
        (G 2).k ≤ KZ - 201) ∧ 0 < slackZ) := by
  decide

theorem dcSlack : 0 < (V.lo : ℝ) * (2 : ℝ) ^ (-(V.k : ℤ)) -
    (w 0 * (((dAbs (G 0)).hi : ℝ) * (2 : ℝ) ^ (-((G 0).k : ℤ))) +
     w 1 * (((dAbs (G 1)).hi : ℝ) * (2 : ℝ) ^ (-((G 1).k : ℤ))) +
     w 2 * (((dAbs (G 2)).hi : ℝ) * (2 : ℝ) ^ (-((G 2).k : ℤ)))) := by
  have hZ : (0 : ℤ) < slackZ := val_facts.2
  have hL : (0 : ℝ) < (slackZ : ℝ) := by exact_mod_cast hZ
  have hk0 : 0 ≤ KZ - V.k := by linarith [val_facts.1.1]
  have hk1 : 0 ≤ KZ - 201 - (G 0).k := by linarith [val_facts.1.2.1]
  have hk2 : 0 ≤ KZ - 201 - (G 1).k := by linarith [val_facts.1.2.2.1]
  have hk3 : 0 ≤ KZ - 201 - (G 2).k := by linarith [val_facts.1.2.2.2]
  have e0 : (2 : ℝ) ^ (KZ - V.k) = (2 : ℝ) ^ KZ * (2 : ℝ) ^ (-(V.k)) := by
    rw [show KZ - V.k = KZ + (-(V.k)) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have f0 : (2 : ℝ) ^ (KZ - 201 - (G 0).k) =
      (2 : ℝ) ^ KZ * ((2 : ℝ) ^ (-(201 : ℤ)) * (2 : ℝ) ^ (-((G 0).k))) := by
    rw [show KZ - 201 - (G 0).k = KZ + (-(201 : ℤ) + -((G 0).k)) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have f1 : (2 : ℝ) ^ (KZ - 201 - (G 1).k) =
      (2 : ℝ) ^ KZ * ((2 : ℝ) ^ (-(201 : ℤ)) * (2 : ℝ) ^ (-((G 1).k))) := by
    rw [show KZ - 201 - (G 1).k = KZ + (-(201 : ℤ) + -((G 1).k)) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have f2 : (2 : ℝ) ^ (KZ - 201 - (G 2).k) =
      (2 : ℝ) ^ KZ * ((2 : ℝ) ^ (-(201 : ℤ)) * (2 : ℝ) ^ (-((G 2).k))) := by
    rw [show KZ - 201 - (G 2).k = KZ + (-(201 : ℤ) + -((G 2).k)) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have he : (slackZ : ℝ) = (2 : ℝ) ^ KZ *
      ((V.lo : ℝ) * (2 : ℝ) ^ (-(V.k : ℤ)) -
        (w 0 * (((dAbs (G 0)).hi : ℝ) * (2 : ℝ) ^ (-((G 0).k : ℤ))) +
         w 1 * (((dAbs (G 1)).hi : ℝ) * (2 : ℝ) ^ (-((G 1).k : ℤ))) +
         w 2 * (((dAbs (G 2)).hi : ℝ) * (2 : ℝ) ^ (-((G 2).k : ℤ))))) := by
    simp only [slackZ, wz0, wz1, wz2, w, w0, w1, w2, s2]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      Int.toNat_of_nonneg hk0, Int.toNat_of_nonneg hk1, Int.toNat_of_nonneg hk2,
      Int.toNat_of_nonneg hk3, e0, f0, f1, f2]
    ring
  rw [he] at hL
  exact pos_of_mul_pos_right hL (zpow_pos (by norm_num) _).le

/-- **The box is positive**: `fTop > 0` on the box, closed by the DC T2
terminal alone (value bracket at the centre + box-wide gradient brackets). -/
theorem Top_pos : ∀ x ∈ D, 0 < fTop x :=
  dcT2_pos (f := fTop) (D := D) (c := c) (w := w)
    c_mem seg_mem Box.JTop_mem.1 w_abs V G V_mem G_mem dcSlack

#print axioms c_mem
#print axioms seg_mem
#print axioms w_abs
#print axioms val_facts
#print axioms dcSlack
#print axioms Top_pos

end

end W1DC15873
end Kepler.Text.TaylorSecond


/-
Kepler.Text.TaylorSecond.W1DCTermPilot — lane `wt1-emission-pilot-w1` (2026-11-25).

**DC-only tree certificate** of the wt1 box `15873/RRLLRL#1` (mode `zero`):
the full 34-node tree of `w1F3Z` emitted as `DCJet` chains via
`Kepler.Text.TaylorSecond.DCJet`, in two passes

  * box pass  `Box.J…`  : `JetMem J… f… D`   on `D = {x | I4.mem (x 0) ∧ …}`,
  * point pass `Pt.J…`  : `JetMem J… f… Dpt` on the degenerate `Dpt = {x | x = c}`,

and the T2 terminal `dcT2_pos` with `V := Pt.JTop.value`, `G i := Box.JTop.part i`.
The slack is decided on ℚ and cast to ℝ (`Rat.cast_zpow`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.TaylorSecond.LeafKit
import Kepler.NliBanks21

set_option maxHeartbeats 32000000
set_option maxRecDepth 2000000
set_option exponentiation.threshold 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCTermPilot

open DCKit
open DCJetKit
open DCMatan
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


/-! ## 2. The shared constant jets (box- and point-independent) -/

def JSI : DCJet := constDC SIbr (Real.sqrt 2)
theorem JSI_mem (E : Set (Fin 3 → ℝ)) : JetMem JSI fSI E :=
  constDC_mem SIbr _ SIbr_mem E

def JPI : DCJet := constDC PIbr (Real.pi)
theorem JPI_mem (E : Set (Fin 3 → ℝ)) : JetMem JPI fPI E :=
  constDC_mem PIbr _ PIbr_mem E

def JMM1 : DCJet := constDC MM1br (mm1)
theorem JMM1_mem (E : Set (Fin 3 → ℝ)) : JetMem JMM1 fMM1 E :=
  constDC_mem MM1br _ MM1br_mem E

def JMM2 : DCJet := constDC MM2br (mm2)
theorem JMM2_mem (E : Set (Fin 3 → ℝ)) : JetMem JMM2 fMM2 E :=
  constDC_mem MM2br _ MM2br_mem E

def JC2 : DCJet := DCJetKit.const (2 : ℤ)
theorem JC2_mem (E : Set (Fin 3 → ℝ)) : JetMem JC2 fC2 E :=
  DCJetKit.const_mem (2 : ℤ) E

def JC4 : DCJet := DCJetKit.const (4 : ℤ)
theorem JC4_mem (E : Set (Fin 3 → ℝ)) : JetMem JC4 fC4 E :=
  DCJetKit.const_mem (4 : ℤ) E

def JC8 : DCJet := DCJetKit.const (8 : ℤ)
theorem JC8_mem (E : Set (Fin 3 → ℝ)) : JetMem JC8 fC8 E :=
  DCJetKit.const_mem (8 : ℤ) E

def JCN2 : DCJet := DCJetKit.const (-2 : ℤ)
theorem JCN2_mem (E : Set (Fin 3 → ℝ)) : JetMem JCN2 fCN2 E :=
  DCJetKit.const_mem (-2 : ℤ) E

def JCH : DCJet := constDC (dDiv (dInt 1) (dInt 2)) (1 / 2 : ℝ)
theorem JCH_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH fCH E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 2)) E

def JCH0 : DCJet := constDC (dDiv (dInt 63) (dInt 50)) (63 / 50 : ℝ)
theorem JCH0_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH0 fCH0 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 63) (dInt_mem 50)) E

def JCH0i : DCJet := constDC (dDiv (dInt 50) (dInt 13)) (50 / 13 : ℝ)
theorem JCH0i_mem (E : Set (Fin 3 → ℝ)) : JetMem JCH0i fCH0i E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 50) (dInt_mem 13)) E

def JC008 : DCJet := constDC (dDiv (dInt 1) (dInt 125)) (1 / 125 : ℝ)
theorem JC008_mem (E : Set (Fin 3 → ℝ)) : JetMem JC008 fC008 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 125)) E

def JC112 : DCJet := constDC (dDiv (dInt 1) (dInt 12)) (1 / 12 : ℝ)
theorem JC112_mem (E : Set (Fin 3 → ℝ)) : JetMem JC112 fC112 E :=
  constDC_mem _ _ (by simpa using dDiv_mem (by decide) (dInt_mem 1) (dInt_mem 12)) E


/-! ## 3. Box pass -/

namespace Box

def JY4 : DCJet := DCJetKit.coord 0 I4
theorem JY4_mem : JetMem JY4 fY4 D :=
  DCJetKit.coord_mem 0 I4 D (fun x hx => hx.1)

def JY5 : DCJet := DCJetKit.coord 1 I5
theorem JY5_mem : JetMem JY5 fY5 D :=
  DCJetKit.coord_mem 1 I5 D (fun x hx => hx.2.1)

def JY6 : DCJet := DCJetKit.coord 2 I6
theorem JY6_mem : JetMem JY6 fY6 D :=
  DCJetKit.coord_mem 2 I6 D (fun x hx => hx.2.2)

def JX4 : DCJet := DCJetKit.mul JY4 JY4
theorem JX4_mem : JetMem JX4 fX4 D :=
  DCJetKit.mul_mem (JY4_mem) (JY4_mem)

def JX5 : DCJet := DCJetKit.mul JY5 JY5
theorem JX5_mem : JetMem JX5 fX5 D :=
  DCJetKit.mul_mem (JY5_mem) (JY5_mem)

def JX6 : DCJet := DCJetKit.mul JY6 JY6
theorem JX6_mem : JetMem JX6 fX6 D :=
  DCJetKit.mul_mem (JY6_mem) (JY6_mem)

def JX4sq : DCJet := DCJetKit.mul JX4 JX4
theorem JX4sq_mem : JetMem JX4sq fX4sq D :=
  DCJetKit.mul_mem (JX4_mem) (JX4_mem)

def JX5sq : DCJet := DCJetKit.mul JX5 JX5
theorem JX5sq_mem : JetMem JX5sq fX5sq D :=
  DCJetKit.mul_mem (JX5_mem) (JX5_mem)

def JX6sq : DCJet := DCJetKit.mul JX6 JX6
theorem JX6sq_mem : JetMem JX6sq fX6sq D :=
  DCJetKit.mul_mem (JX6_mem) (JX6_mem)

def JS2a : DCJet := DCJetKit.add JX4sq JX5sq
theorem JS2a_mem : JetMem JS2a fS2a D :=
  DCJetKit.add_mem (JX4sq_mem) (JX5sq_mem)

def JS2 : DCJet := DCJetKit.add JS2a JX6sq
theorem JS2_mem : JetMem JS2 fS2 D :=
  DCJetKit.add_mem (JS2a_mem) (JX6sq_mem)

def JX4X5 : DCJet := DCJetKit.mul JX4 JX5
theorem JX4X5_mem : JetMem JX4X5 fX4X5 D :=
  DCJetKit.mul_mem (JX4_mem) (JX5_mem)

def JX4X6 : DCJet := DCJetKit.mul JX4 JX6
theorem JX4X6_mem : JetMem JX4X6 fX4X6 D :=
  DCJetKit.mul_mem (JX4_mem) (JX6_mem)

def JX5X6 : DCJet := DCJetKit.mul JX5 JX6
theorem JX5X6_mem : JetMem JX5X6 fX5X6 D :=
  DCJetKit.mul_mem (JX5_mem) (JX6_mem)

def JS1a : DCJet := DCJetKit.add JX4X5 JX4X6
theorem JS1a_mem : JetMem JS1a fS1a D :=
  DCJetKit.add_mem (JX4X5_mem) (JX4X6_mem)

def JS1 : DCJet := DCJetKit.add JS1a JX5X6
theorem JS1_mem : JetMem JS1 fS1 D :=
  DCJetKit.add_mem (JS1a_mem) (JX5X6_mem)

def JCN2S2 : DCJet := DCJetKit.mul JCN2 JS2
theorem JCN2S2_mem : JetMem JCN2S2 fCN2S2 D :=
  DCJetKit.mul_mem (JCN2_mem D) (JS2_mem)

def JC4S1 : DCJet := DCJetKit.mul JC4 JS1
theorem JC4S1_mem : JetMem JC4S1 fC4S1 D :=
  DCJetKit.mul_mem (JC4_mem D) (JS1_mem)

def JDltA : DCJet := DCJetKit.add JCN2S2 JC4S1
theorem JDltA_mem : JetMem JDltA fDltA D :=
  DCJetKit.add_mem (JCN2S2_mem) (JC4S1_mem)

def JX4X5X6 : DCJet := DCJetKit.mul JX4X5 JX6
theorem JX4X5X6_mem : JetMem JX4X5X6 fX4X5X6 D :=
  DCJetKit.mul_mem (JX4X5_mem) (JX6_mem)

def JDlt : DCJet := DCJetKit.sub JDltA JX4X5X6
theorem JDlt_mem : JetMem JDlt fDlt D :=
  DCJetKit.sub_mem (JDltA_mem) (JX4X5X6_mem)

end Box


/-! ## 3b. The point coordinate brackets -/

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

def JY5 : DCJet := DCJetKit.coord 1 P5
theorem JY5_mem : JetMem JY5 fY5 Dpt :=
  DCJetKit.coord_mem 1 P5 Dpt (fun x hx => by rw [show x = c from hx]; exact P5_mem)

def JY6 : DCJet := DCJetKit.coord 2 P6
theorem JY6_mem : JetMem JY6 fY6 Dpt :=
  DCJetKit.coord_mem 2 P6 Dpt (fun x hx => by rw [show x = c from hx]; exact P6_mem)

def JX4 : DCJet := DCJetKit.mul JY4 JY4
theorem JX4_mem : JetMem JX4 fX4 Dpt :=
  DCJetKit.mul_mem (JY4_mem) (JY4_mem)

def JX5 : DCJet := DCJetKit.mul JY5 JY5
theorem JX5_mem : JetMem JX5 fX5 Dpt :=
  DCJetKit.mul_mem (JY5_mem) (JY5_mem)

def JX6 : DCJet := DCJetKit.mul JY6 JY6
theorem JX6_mem : JetMem JX6 fX6 Dpt :=
  DCJetKit.mul_mem (JY6_mem) (JY6_mem)

def JX4sq : DCJet := DCJetKit.mul JX4 JX4
theorem JX4sq_mem : JetMem JX4sq fX4sq Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX4_mem)

def JX5sq : DCJet := DCJetKit.mul JX5 JX5
theorem JX5sq_mem : JetMem JX5sq fX5sq Dpt :=
  DCJetKit.mul_mem (JX5_mem) (JX5_mem)

def JX6sq : DCJet := DCJetKit.mul JX6 JX6
theorem JX6sq_mem : JetMem JX6sq fX6sq Dpt :=
  DCJetKit.mul_mem (JX6_mem) (JX6_mem)

def JS2a : DCJet := DCJetKit.add JX4sq JX5sq
theorem JS2a_mem : JetMem JS2a fS2a Dpt :=
  DCJetKit.add_mem (JX4sq_mem) (JX5sq_mem)

def JS2 : DCJet := DCJetKit.add JS2a JX6sq
theorem JS2_mem : JetMem JS2 fS2 Dpt :=
  DCJetKit.add_mem (JS2a_mem) (JX6sq_mem)

def JX4X5 : DCJet := DCJetKit.mul JX4 JX5
theorem JX4X5_mem : JetMem JX4X5 fX4X5 Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX5_mem)

def JX4X6 : DCJet := DCJetKit.mul JX4 JX6
theorem JX4X6_mem : JetMem JX4X6 fX4X6 Dpt :=
  DCJetKit.mul_mem (JX4_mem) (JX6_mem)

def JX5X6 : DCJet := DCJetKit.mul JX5 JX6
theorem JX5X6_mem : JetMem JX5X6 fX5X6 Dpt :=
  DCJetKit.mul_mem (JX5_mem) (JX6_mem)

def JS1a : DCJet := DCJetKit.add JX4X5 JX4X6
theorem JS1a_mem : JetMem JS1a fS1a Dpt :=
  DCJetKit.add_mem (JX4X5_mem) (JX4X6_mem)

def JS1 : DCJet := DCJetKit.add JS1a JX5X6
theorem JS1_mem : JetMem JS1 fS1 Dpt :=
  DCJetKit.add_mem (JS1a_mem) (JX5X6_mem)

def JCN2S2 : DCJet := DCJetKit.mul JCN2 JS2
theorem JCN2S2_mem : JetMem JCN2S2 fCN2S2 Dpt :=
  DCJetKit.mul_mem (JCN2_mem Dpt) (JS2_mem)

def JC4S1 : DCJet := DCJetKit.mul JC4 JS1
theorem JC4S1_mem : JetMem JC4S1 fC4S1 Dpt :=
  DCJetKit.mul_mem (JC4_mem Dpt) (JS1_mem)

def JDltA : DCJet := DCJetKit.add JCN2S2 JC4S1
theorem JDltA_mem : JetMem JDltA fDltA Dpt :=
  DCJetKit.add_mem (JCN2S2_mem) (JC4S1_mem)

def JX4X5X6 : DCJet := DCJetKit.mul JX4X5 JX6
theorem JX4X5X6_mem : JetMem JX4X5X6 fX4X5X6 Dpt :=
  DCJetKit.mul_mem (JX4X5_mem) (JX6_mem)

def JDlt : DCJet := DCJetKit.sub JDltA JX4X5X6
theorem JDlt_mem : JetMem JDlt fDlt Dpt :=
  DCJetKit.sub_mem (JDltA_mem) (JX4X5X6_mem)

end Pt


/-! ## 5. The T2 terminal -/

def V : DC := Pt.JDlt.value

def G : Fin 3 → DC := fun i => Box.JDlt.part i

theorem V_mem : V.mem (fDlt c) := by
  have h := Pt.JDlt_mem
  exact h.2.1 c (show c ∈ Dpt from rfl)

theorem G_mem : ∀ x ∈ D, ∀ i, (G i).mem (partial1 i fDlt x) := by
  intro x hx i
  exact Box.JDlt_mem.2.2 x hx i

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
kernel computation. -/
theorem val_facts :
    ((V.k ≤ KZ ∧ (G 0).k ≤ KZ - 201 ∧ (G 1).k ≤ KZ - 201 ∧
        (G 2).k ≤ KZ - 201) ∧ 0 < slackZ) := by decide

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

/-- **The box is positive**: `fDlt > 0` on the box, closed by the DC T2
terminal alone (value bracket at the centre + box-wide gradient brackets). -/
theorem Dlt_pos : ∀ x ∈ D, 0 < fDlt x :=
  dcT2_pos (f := fDlt) (D := D) (c := c) (w := w)
    c_mem seg_mem Box.JDlt_mem.1 w_abs V G V_mem G_mem dcSlack

#print axioms c_mem
#print axioms seg_mem
#print axioms w_abs
#print axioms val_facts
#print axioms dcSlack
#print axioms Dlt_pos

end

end W1DCTermPilot
end Kepler.Text.TaylorSecond


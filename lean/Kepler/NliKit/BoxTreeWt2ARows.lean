/-
Kepler.NliKit.BoxTreeWt2ARows — shared data tables for the wt2A tree replay
(lane nlikit-boxtree-impl-w1; machine-generated, PYTHONHASHSEED=0,
input sha256 e64fd7844d03b448cc6b033a96dd471f66fff682685e7536b83bd076c8dbbef3).  Endpoints on the 2^-40 dyadic grid; every
fact below is decide/norm_num/rfl — zero new axioms.
-/
import Kepler.NliBanks27
import Kepler.NliKit.BoxTree

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem kNat0 : ((0 : ℤ).toNat) = 0 := rfl
theorem kNat40 : ((40 : ℤ).toNat) = 40 := rfl

theorem sqrt8_br : (2.82842712:ℝ) ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ (2.82842713:ℝ) := by
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2.82842713)]
    norm_num

/-- domain-folded target predicate (w1 T-4). -/
def PWt2A : (Fin 3 → ℝ) → Prop := fun x =>
  (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
  (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
  (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
  (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
  (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)

def topLoWt2A : Fin 3 → DC := fun i => match (i : ℕ) with
  | 0 => (⟨40, 2708646895026, 2708646895026⟩ : DC)  -- shell lo ↓
  | 1 => (⟨40, 2708646895026, 2708646895026⟩ : DC)
  | _ => (⟨40, 2199023255552, 2199023255552⟩ : DC)
def topHiWt2A : Fin 3 → DC := fun i => match (i : ℕ) with
  | 0 => (⟨40, 3109888511976, 3109888511976⟩ : DC)  -- shell hi ↑
  | 1 => (⟨40, 3109888511976, 3109888511976⟩ : DC)  -- shell hi ↑
  | _ => (⟨40, 2708668885259, 2708668885259⟩ : DC)  -- shell hi ↑

/-- dyadic cuts: one grid step strictly below each decimal plane;
EQNAMEs content-derived (axis + plane digits). -/
def cA0_129855339_50000000 : DC := (⟨40, 2855549103185, 2855549103185⟩ : DC)
def cA0_137566017_50000000 : DC := (⟨40, 3025108705566, 3025108705566⟩ : DC)
def cA0_19821_8000 : DC := (⟨40, 2724177496768, 2724177496768⟩ : DC)
def cA0_20047_8000 : DC := (⟨40, 2755238700253, 2755238700253⟩ : DC)
def cA0_255855339_100000000 : DC := (⟨40, 2813159202590, 2813159202590⟩ : DC)
def cA0_63_25 : DC := (⟨40, 2770769301995, 2770769301995⟩ : DC)
def cA0_66855339_25000000 : DC := (⟨40, 2940328904376, 2940328904376⟩ : DC)
def cA0_9967_4000 : DC := (⟨40, 2739708098510, 2739708098510⟩ : DC)
def cA1_19821_8000 : DC := (⟨40, 2724177496768, 2724177496768⟩ : DC)
def cA1_63_25 : DC := (⟨40, 2770769301995, 2770769301995⟩ : DC)
def cA1_66855339_25000000 : DC := (⟨40, 2940328904376, 2940328904376⟩ : DC)
def cA1_9967_4000 : DC := (⟨40, 2739708098510, 2739708098510⟩ : DC)
def cA2_1029_500 : DC := (⟨40, 2262794929963, 2262794929963⟩ : DC)
def cA2_1087_500 : DC := (⟨40, 2390338278785, 2390338278785⟩ : DC)
def cA2_2347_1000 : DC := (⟨40, 2580553790390, 2580553790390⟩ : DC)

/-- value bridges per distinct point literal (norm_num on pure literals). -/
theorem vB40_2199023255552 : (⟨(40 : ℤ), 2199023255552, 2199023255552⟩ : DC).value = (2199023255552:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2262794929963 : (⟨(40 : ℤ), 2262794929963, 2262794929963⟩ : DC).value = (2262794929963:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2390338278785 : (⟨(40 : ℤ), 2390338278785, 2390338278785⟩ : DC).value = (2390338278785:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2580553790390 : (⟨(40 : ℤ), 2580553790390, 2580553790390⟩ : DC).value = (2580553790390:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2708646895026 : (⟨(40 : ℤ), 2708646895026, 2708646895026⟩ : DC).value = (2708646895026:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2708668885259 : (⟨(40 : ℤ), 2708668885259, 2708668885259⟩ : DC).value = (2708668885259:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2724177496768 : (⟨(40 : ℤ), 2724177496768, 2724177496768⟩ : DC).value = (2724177496768:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2739708098510 : (⟨(40 : ℤ), 2739708098510, 2739708098510⟩ : DC).value = (2739708098510:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2755238700253 : (⟨(40 : ℤ), 2755238700253, 2755238700253⟩ : DC).value = (2755238700253:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2770769301995 : (⟨(40 : ℤ), 2770769301995, 2770769301995⟩ : DC).value = (2770769301995:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2813159202590 : (⟨(40 : ℤ), 2813159202590, 2813159202590⟩ : DC).value = (2813159202590:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2855549103185 : (⟨(40 : ℤ), 2855549103185, 2855549103185⟩ : DC).value = (2855549103185:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2940328904376 : (⟨(40 : ℤ), 2940328904376, 2940328904376⟩ : DC).value = (2940328904376:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_3025108705566 : (⟨(40 : ℤ), 3025108705566, 3025108705566⟩ : DC).value = (3025108705566:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_3109888511976 : (⟨(40 : ℤ), 3109888511976, 3109888511976⟩ : DC).value = (3109888511976:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num

/-- cut DC-identity facts (rfl). -/
theorem cA0_129855339_50000000_eq : cA0_129855339_50000000 = (⟨40, 2855549103185, 2855549103185⟩ : DC) := rfl
theorem cA0_137566017_50000000_eq : cA0_137566017_50000000 = (⟨40, 3025108705566, 3025108705566⟩ : DC) := rfl
theorem cA0_19821_8000_eq : cA0_19821_8000 = (⟨40, 2724177496768, 2724177496768⟩ : DC) := rfl
theorem cA0_20047_8000_eq : cA0_20047_8000 = (⟨40, 2755238700253, 2755238700253⟩ : DC) := rfl
theorem cA0_255855339_100000000_eq : cA0_255855339_100000000 = (⟨40, 2813159202590, 2813159202590⟩ : DC) := rfl
theorem cA0_63_25_eq : cA0_63_25 = (⟨40, 2770769301995, 2770769301995⟩ : DC) := rfl
theorem cA0_66855339_25000000_eq : cA0_66855339_25000000 = (⟨40, 2940328904376, 2940328904376⟩ : DC) := rfl
theorem cA0_9967_4000_eq : cA0_9967_4000 = (⟨40, 2739708098510, 2739708098510⟩ : DC) := rfl
theorem cA1_19821_8000_eq : cA1_19821_8000 = (⟨40, 2724177496768, 2724177496768⟩ : DC) := rfl
theorem cA1_63_25_eq : cA1_63_25 = (⟨40, 2770769301995, 2770769301995⟩ : DC) := rfl
theorem cA1_66855339_25000000_eq : cA1_66855339_25000000 = (⟨40, 2940328904376, 2940328904376⟩ : DC) := rfl
theorem cA1_9967_4000_eq : cA1_9967_4000 = (⟨40, 2739708098510, 2739708098510⟩ : DC) := rfl
theorem cA2_1029_500_eq : cA2_1029_500 = (⟨40, 2262794929963, 2262794929963⟩ : DC) := rfl
theorem cA2_1087_500_eq : cA2_1087_500 = (⟨40, 2390338278785, 2390338278785⟩ : DC) := rfl
theorem cA2_2347_1000_eq : cA2_2347_1000 = (⟨40, 2580553790390, 2580553790390⟩ : DC) := rfl

/-- node box endpoint identities at the cut axis (kernel-decide). -/
theorem nlo_0 : (topLoWt2A (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_0 : (Function.update (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000) 0 cA0_19821_8000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_1 : (Function.update (topLoWt2A) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_1 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000) 0 cA0_19821_8000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_2 : (topLoWt2A (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_2 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000) 0 cA0_19821_8000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_3 : (Function.update (topLoWt2A) 0 cA0_19821_8000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_3 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_4 : (Function.update (Function.update (topLoWt2A) 0 cA0_19821_8000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_4 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_5 : (Function.update (topLoWt2A) 0 cA0_19821_8000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_5 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_6 : (topLoWt2A (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_6 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_9967_4000 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nlo_7 : (Function.update (topLoWt2A) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_7 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_20047_8000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_8 : (Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_8 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_20047_8000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_9 : (Function.update (topLoWt2A) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_9 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_20047_8000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_10 : (Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 0 cA0_20047_8000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_10 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_11 : (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 0 cA0_20047_8000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_11 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_12 : (Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 0 cA0_20047_8000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_12 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_13 : (Function.update (topLoWt2A) 0 cA0_9967_4000 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nhi_13 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_14 : (topLoWt2A (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_14 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_15 : (Function.update (topLoWt2A) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_15 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_9967_4000) 0 cA0_255855339_100000000 (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nlo_16 : (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_255855339_100000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_16 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_9967_4000 (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nlo_17 : (Function.update (topLoWt2A) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_17 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_9967_4000 (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem nlo_18 : (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_9967_4000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_18 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_19 : (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_9967_4000 (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nhi_19 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_20 : (Function.update (topLoWt2A) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_20 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_21 : (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_21 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_22 : (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_22 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_23 : (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_23 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_24 : (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000) 0 cA0_66855339_25000000 (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem nhi_24 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_9967_4000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_25 : (Function.update (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000) 0 cA0_66855339_25000000) 1 cA1_9967_4000 (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem nhi_25 : (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_26 : (Function.update (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000) 0 cA0_66855339_25000000) 1 cA1_9967_4000 (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nhi_26 : (Function.update (topHiWt2A) 2 cA2_1029_500 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_27 : (Function.update (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_27 : (Function.update (topHiWt2A) 2 cA2_1029_500 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_28 : (Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 0 cA0_129855339_50000000 (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem nhi_28 : (Function.update (topHiWt2A) 2 cA2_1029_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_29 : (Function.update (topLoWt2A) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_29 : (Function.update (topHiWt2A) 2 cA2_1029_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_30 : (topLoWt2A (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_30 : (Function.update (topHiWt2A) 2 cA2_1029_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_31 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_31 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 0 cA0_9967_4000) 1 cA1_66855339_25000000 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nlo_32 : (Function.update (topLoWt2A) 2 cA2_1029_500 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_32 : (Function.update (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 0 cA0_9967_4000) 1 cA1_66855339_25000000 (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem nlo_33 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_66855339_25000000 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_33 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 0 cA0_9967_4000 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nlo_34 : (Function.update (topLoWt2A) 2 cA2_1029_500 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_34 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_35 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nhi_35 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 1 cA1_66855339_25000000 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_36 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_36 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 1 cA1_66855339_25000000 (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem nlo_37 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_66855339_25000000 (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem nhi_37 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_38 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_38 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_39 : (Function.update (topLoWt2A) 2 cA2_1029_500 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_39 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_40 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_40 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_41 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_41 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_42 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 0 cA0_129855339_50000000 (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem nhi_42 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_43 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_43 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_44 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_44 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_45 : (Function.update (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25) 0 cA0_129855339_50000000 (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_45 : (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_46 : (Function.update (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25) 0 cA0_129855339_50000000 (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem nhi_46 : (Function.update (topHiWt2A) 2 cA2_1087_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_47 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_47 : (Function.update (topHiWt2A) 2 cA2_1087_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_48 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_48 : (Function.update (topHiWt2A) 2 cA2_1087_500 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_49 : (Function.update (topLoWt2A) 2 cA2_1029_500 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_49 : (Function.update (topHiWt2A) 2 cA2_1087_500 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_50 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_50 : (Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_63_25) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_51 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500) 0 cA0_9967_4000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_51 : (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_52 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_52 : (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nlo_53 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500) 0 cA0_63_25 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_53 : (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_54 : (Function.update (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500) 0 cA0_63_25) 0 cA0_66855339_25000000 (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_54 : (Function.update (topHiWt2A) 2 cA2_2347_1000 (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_55 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500) 0 cA0_63_25 (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem nhi_55 : (Function.update (topHiWt2A) 2 cA2_2347_1000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_56 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_56 : (Function.update (topHiWt2A) 2 cA2_2347_1000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_57 : (Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500) 2 cA2_2347_1000 (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem nhi_57 : (topHiWt2A (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_58 : (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 2 cA2_1087_500 (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem nhi_58 : (topHiWt2A (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_59 : (Function.update (topLoWt2A) 2 cA2_1029_500 (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem nhi_59 : (topHiWt2A (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_60 : (topLoWt2A (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_60 : (topHiWt2A (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide

/-- leaf table: endpoints are the EXACT tree-path expressions, so every
`Cover.leaf` obligation closes by `rfl` (identical terms). -/
def rowsWt2A : Fin 62 → LeafRow 3 Unit := fun j => match (j : ℕ) with
  | 0 => { boxLo := topLoWt2A, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_19821_8000) 1 cA1_9967_4000, aux := () }
  | 1 => { boxLo := Function.update (topLoWt2A) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_19821_8000) 1 cA1_63_25, aux := () }
  | 2 => { boxLo := Function.update (topLoWt2A) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_19821_8000) 1 cA1_66855339_25000000, aux := () }
  | 3 => { boxLo := Function.update (topLoWt2A) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_19821_8000, aux := () }
  | 4 => { boxLo := Function.update (topLoWt2A) 0 cA0_19821_8000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_9967_4000, aux := () }
  | 5 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_19821_8000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_63_25, aux := () }
  | 6 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_19821_8000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_66855339_25000000, aux := () }
  | 7 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_19821_8000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_9967_4000, aux := () }
  | 8 => { boxLo := Function.update (topLoWt2A) 0 cA0_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_20047_8000) 1 cA1_9967_4000, aux := () }
  | 9 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_20047_8000) 1 cA1_63_25, aux := () }
  | 10 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_20047_8000) 1 cA1_66855339_25000000, aux := () }
  | 11 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_9967_4000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_20047_8000, aux := () }
  | 12 => { boxLo := Function.update (topLoWt2A) 0 cA0_20047_8000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_9967_4000, aux := () }
  | 13 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_20047_8000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25, aux := () }
  | 14 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_20047_8000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_66855339_25000000, aux := () }
  | 15 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_20047_8000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_63_25, aux := () }
  | 16 => { boxLo := Function.update (topLoWt2A) 0 cA0_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_255855339_100000000) 1 cA1_19821_8000, aux := () }
  | 17 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_19821_8000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_255855339_100000000) 1 cA1_9967_4000, aux := () }
  | 18 => { boxLo := Function.update (topLoWt2A) 0 cA0_255855339_100000000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_19821_8000, aux := () }
  | 19 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_255855339_100000000) 1 cA1_19821_8000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_9967_4000, aux := () }
  | 20 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_63_25, aux := () }
  | 21 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_66855339_25000000, aux := () }
  | 22 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_63_25) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000, aux := () }
  | 23 => { boxLo := Function.update (topLoWt2A) 0 cA0_129855339_50000000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000) 1 cA1_9967_4000, aux := () }
  | 24 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_129855339_50000000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000) 1 cA1_63_25, aux := () }
  | 25 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_129855339_50000000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000) 1 cA1_66855339_25000000, aux := () }
  | 26 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_129855339_50000000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000, aux := () }
  | 27 => { boxLo := Function.update (topLoWt2A) 0 cA0_66855339_25000000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_9967_4000) 0 cA0_137566017_50000000, aux := () }
  | 28 => { boxLo := Function.update (topLoWt2A) 0 cA0_137566017_50000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_9967_4000, aux := () }
  | 29 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_66855339_25000000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_63_25) 0 cA0_137566017_50000000, aux := () }
  | 30 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_137566017_50000000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1029_500) 1 cA1_63_25, aux := () }
  | 31 => { boxLo := Function.update (Function.update (topLoWt2A) 0 cA0_66855339_25000000) 1 cA1_63_25, boxHi := Function.update (topHiWt2A) 2 cA2_1029_500, aux := () }
  | 32 => { boxLo := Function.update (topLoWt2A) 2 cA2_1029_500, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_9967_4000) 1 cA1_63_25, aux := () }
  | 33 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_19821_8000) 1 cA1_66855339_25000000, aux := () }
  | 34 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_63_25) 0 cA0_19821_8000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_9967_4000) 1 cA1_66855339_25000000, aux := () }
  | 35 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_19821_8000, aux := () }
  | 36 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 1 cA1_66855339_25000000) 0 cA0_19821_8000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_9967_4000, aux := () }
  | 37 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 1 cA1_63_25, aux := () }
  | 38 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_20047_8000) 1 cA1_66855339_25000000, aux := () }
  | 39 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_20047_8000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25) 1 cA1_66855339_25000000, aux := () }
  | 40 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_9967_4000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_20047_8000, aux := () }
  | 41 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_20047_8000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_63_25, aux := () }
  | 42 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_9967_4000) 0 cA0_129855339_50000000, aux := () }
  | 43 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25) 0 cA0_129855339_50000000, aux := () }
  | 44 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_9967_4000) 0 cA0_66855339_25000000, aux := () }
  | 45 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25) 0 cA0_66855339_25000000, aux := () }
  | 46 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 1 cA1_63_25, aux := () }
  | 47 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_129855339_50000000) 1 cA1_66855339_25000000, aux := () }
  | 48 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_63_25) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_129855339_50000000, aux := () }
  | 49 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_66855339_25000000) 1 cA1_66855339_25000000, aux := () }
  | 50 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_129855339_50000000) 1 cA1_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_1087_500) 0 cA0_66855339_25000000, aux := () }
  | 51 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1029_500) 0 cA0_66855339_25000000) 1 cA1_63_25, boxHi := Function.update (topHiWt2A) 2 cA2_1087_500, aux := () }
  | 52 => { boxLo := Function.update (topLoWt2A) 2 cA2_1087_500, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_9967_4000) 1 cA1_63_25, aux := () }
  | 53 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 1 cA1_63_25, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_9967_4000, aux := () }
  | 54 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_9967_4000, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_63_25) 1 cA1_63_25, aux := () }
  | 55 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_9967_4000) 1 cA1_63_25, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_63_25, aux := () }
  | 56 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_63_25, boxHi := Function.update (Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_66855339_25000000) 1 cA1_63_25, aux := () }
  | 57 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_63_25) 1 cA1_63_25, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 0 cA0_66855339_25000000, aux := () }
  | 58 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_66855339_25000000, boxHi := Function.update (Function.update (topHiWt2A) 2 cA2_2347_1000) 1 cA1_63_25, aux := () }
  | 59 => { boxLo := Function.update (Function.update (Function.update (topLoWt2A) 2 cA2_1087_500) 0 cA0_66855339_25000000) 1 cA1_63_25, boxHi := Function.update (topHiWt2A) 2 cA2_2347_1000, aux := () }
  | 60 => { boxLo := Function.update (topLoWt2A) 2 cA2_2347_1000, boxHi := Function.update (topHiWt2A) 0 cA0_63_25, aux := () }
  | 61 => { boxLo := Function.update (Function.update (topLoWt2A) 2 cA2_2347_1000) 0 cA0_63_25, boxHi := topHiWt2A, aux := () }
  | _ => { boxLo := topLoWt2A, boxHi := topHiWt2A, aux := () }

def leafPassWt2A : Fin 62 → Bool := fun _ => true

end Kepler.NliKit.BoxTreeWt2A

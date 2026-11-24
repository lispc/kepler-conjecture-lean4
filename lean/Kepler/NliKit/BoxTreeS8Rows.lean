/-
Kepler.NliKit.BoxTreeS8Rows — shared data tables for the sqrt8 tree replay
(lane nlikit-boxtree-impl-w1; machine-generated, PYTHONHASHSEED=0,
input sha256 1a782c0b41746f71da247b0dcd5b734d3297e2726ab9c47fb5c67de75f4a3850).  Endpoints on the 2^-40 dyadic grid; every
fact below is decide/norm_num/rfl — zero new axioms.
-/
import Kepler.Text.NliSqrt8
import Kepler.NliKit.BoxTree

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem kNat0 : ((0 : ℤ).toNat) = 0 := rfl
theorem kNat40 : ((40 : ℤ).toNat) = 40 := rfl

theorem sqrt8_br : (2.82842712:ℝ) ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ (2.82842713:ℝ) := by
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2.82842713)]
    norm_num

theorem s8hp : (2:ℝ) * Kepler.Text.hplus = (2.6508:ℝ) := by norm_num [Kepler.Text.hplus]

/-- domain-folded target predicate (w1 T-4). -/
def PS8 : (Fin 3 → ℝ) → Prop := fun x =>
  (2:ℝ) * Kepler.Text.hplus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
  (2:ℝ) ≤ x 1 → x 1 ≤ (2:ℝ) * Kepler.Text.hminus →
  (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
  x 1 ≤ x 2 →
  (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
  (0:ℝ) < Kepler.NliBanks11.c3Main (x 0) (x 1) (x 2)

def topLoS8 : Fin 3 → DC := fun i => match (i : ℕ) with
  | 0 => (⟨40, 2914585422908, 2914585422908⟩ : DC)  -- shell lo ↓
  | 1 => (⟨40, 2199023255552, 2199023255552⟩ : DC)
  | _ => (⟨40, 2199023255552, 2199023255552⟩ : DC)
def topHiS8 : Fin 3 → DC := fun i => match (i : ℕ) with
  | 0 => (⟨40, 3109888511976, 3109888511976⟩ : DC)  -- shell hi ↑
  | 1 => (⟨40, 2708668885259, 2708668885259⟩ : DC)  -- shell hi ↑
  | _ => (⟨40, 2708668885259, 2708668885259⟩ : DC)  -- shell hi ↑

/-- dyadic cuts: one grid step strictly below each decimal plane;
EQNAMEs content-derived (axis + plane digits). -/
def cA0_139_50 : DC := (⟨40, 3056642325217, 3056642325217⟩ : DC)
def cA0_2683_1000 : DC := (⟨40, 2949989697323, 2949989697323⟩ : DC)
def cA0_68_25 : DC := (⟨40, 2990671627550, 2990671627550⟩ : DC)
def cA1_102897_50000 : DC := (⟨40, 2262728959265, 2262728959265⟩ : DC)
def cA1_108691_50000 : DC := (⟨40, 2390140366692, 2390140366692⟩ : DC)
def cA1_202897_100000 : DC := (⟨40, 2230876107408, 2230876107408⟩ : DC)
def cA1_27897_12500 : DC := (⟨40, 2453846070405, 2453846070405⟩ : DC)
def cA1_52897_25000 : DC := (⟨40, 2326434662978, 2326434662978⟩ : DC)
def cA1_58691_25000 : DC := (⟨40, 2581257477832, 2581257477832⟩ : DC)
def cA2_102897_50000 : DC := (⟨40, 2262728959265, 2262728959265⟩ : DC)
def cA2_108691_50000 : DC := (⟨40, 2390140366692, 2390140366692⟩ : DC)
def cA2_202897_100000 : DC := (⟨40, 2230876107408, 2230876107408⟩ : DC)
def cA2_27897_12500 : DC := (⟨40, 2453846070405, 2453846070405⟩ : DC)
def cA2_52897_25000 : DC := (⟨40, 2326434662978, 2326434662978⟩ : DC)
def cA2_58691_25000 : DC := (⟨40, 2581257477832, 2581257477832⟩ : DC)

/-- value bridges per distinct point literal (norm_num on pure literals). -/
theorem vB40_2199023255552 : (⟨(40 : ℤ), 2199023255552, 2199023255552⟩ : DC).value = (2199023255552:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2230876107408 : (⟨(40 : ℤ), 2230876107408, 2230876107408⟩ : DC).value = (2230876107408:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2262728959265 : (⟨(40 : ℤ), 2262728959265, 2262728959265⟩ : DC).value = (2262728959265:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2326434662978 : (⟨(40 : ℤ), 2326434662978, 2326434662978⟩ : DC).value = (2326434662978:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2390140366692 : (⟨(40 : ℤ), 2390140366692, 2390140366692⟩ : DC).value = (2390140366692:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2453846070405 : (⟨(40 : ℤ), 2453846070405, 2453846070405⟩ : DC).value = (2453846070405:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2581257477832 : (⟨(40 : ℤ), 2581257477832, 2581257477832⟩ : DC).value = (2581257477832:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2708668885259 : (⟨(40 : ℤ), 2708668885259, 2708668885259⟩ : DC).value = (2708668885259:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2914585422908 : (⟨(40 : ℤ), 2914585422908, 2914585422908⟩ : DC).value = (2914585422908:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2949989697323 : (⟨(40 : ℤ), 2949989697323, 2949989697323⟩ : DC).value = (2949989697323:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_2990671627550 : (⟨(40 : ℤ), 2990671627550, 2990671627550⟩ : DC).value = (2990671627550:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_3056642325217 : (⟨(40 : ℤ), 3056642325217, 3056642325217⟩ : DC).value = (3056642325217:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num
theorem vB40_3109888511976 : (⟨(40 : ℤ), 3109888511976, 3109888511976⟩ : DC).value = (3109888511976:ℝ)/1099511627776 := by
  simp [DC.value, kNat40]
  norm_num

/-- cut DC-identity facts (rfl). -/
theorem cA0_139_50_eq : cA0_139_50 = (⟨40, 3056642325217, 3056642325217⟩ : DC) := rfl
theorem cA0_2683_1000_eq : cA0_2683_1000 = (⟨40, 2949989697323, 2949989697323⟩ : DC) := rfl
theorem cA0_68_25_eq : cA0_68_25 = (⟨40, 2990671627550, 2990671627550⟩ : DC) := rfl
theorem cA1_102897_50000_eq : cA1_102897_50000 = (⟨40, 2262728959265, 2262728959265⟩ : DC) := rfl
theorem cA1_108691_50000_eq : cA1_108691_50000 = (⟨40, 2390140366692, 2390140366692⟩ : DC) := rfl
theorem cA1_202897_100000_eq : cA1_202897_100000 = (⟨40, 2230876107408, 2230876107408⟩ : DC) := rfl
theorem cA1_27897_12500_eq : cA1_27897_12500 = (⟨40, 2453846070405, 2453846070405⟩ : DC) := rfl
theorem cA1_52897_25000_eq : cA1_52897_25000 = (⟨40, 2326434662978, 2326434662978⟩ : DC) := rfl
theorem cA1_58691_25000_eq : cA1_58691_25000 = (⟨40, 2581257477832, 2581257477832⟩ : DC) := rfl
theorem cA2_102897_50000_eq : cA2_102897_50000 = (⟨40, 2262728959265, 2262728959265⟩ : DC) := rfl
theorem cA2_108691_50000_eq : cA2_108691_50000 = (⟨40, 2390140366692, 2390140366692⟩ : DC) := rfl
theorem cA2_202897_100000_eq : cA2_202897_100000 = (⟨40, 2230876107408, 2230876107408⟩ : DC) := rfl
theorem cA2_27897_12500_eq : cA2_27897_12500 = (⟨40, 2453846070405, 2453846070405⟩ : DC) := rfl
theorem cA2_52897_25000_eq : cA2_52897_25000 = (⟨40, 2326434662978, 2326434662978⟩ : DC) := rfl
theorem cA2_58691_25000_eq : cA2_58691_25000 = (⟨40, 2581257477832, 2581257477832⟩ : DC) := rfl

/-- node box endpoint identities at the cut axis (kernel-decide). -/
theorem nlo_0 : (topLoS8 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_0 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_2683_1000) 1 cA1_202897_100000 (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem nlo_1 : (topLoS8 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_1 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_2683_1000 (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem nlo_2 : (Function.update (topLoS8) 0 cA0_2683_1000 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_2 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25) 1 cA1_102897_50000) 2 cA2_102897_50000 (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem nlo_3 : (topLoS8 (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem nhi_3 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25) 1 cA1_102897_50000) 2 cA2_102897_50000 (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem nlo_4 : (topLoS8 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_4 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25) 1 cA1_102897_50000 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_5 : (Function.update (topLoS8) 1 cA1_102897_50000 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_5 : (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_6 : (topLoS8 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_6 : (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25 (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_7 : (Function.update (topLoS8) 0 cA0_68_25 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_7 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_139_50 (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem nlo_8 : (Function.update (topLoS8) 0 cA0_68_25 (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem nhi_8 : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 1 cA1_102897_50000) 2 cA2_102897_50000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_9 : (Function.update (topLoS8) 0 cA0_68_25 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_9 : (Function.update (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000) 1 cA1_102897_50000 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_10 : (Function.update (Function.update (topLoS8) 0 cA0_68_25) 1 cA1_102897_50000 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_10 : (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_11 : (Function.update (topLoS8) 0 cA0_68_25 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_11 : (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000 (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nlo_12 : (topLoS8 (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem nhi_12 : (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 2 cA2_52897_25000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_13 : (Function.update (topLoS8) 2 cA2_52897_25000 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nhi_13 : (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000) 0 cA0_68_25 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_14 : (Function.update (Function.update (topLoS8) 2 cA2_52897_25000) 0 cA0_68_25 (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nhi_14 : (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_15 : (Function.update (topLoS8) 2 cA2_52897_25000 (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem nhi_15 : (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_16 : (topLoS8 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_16 : (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 1 cA1_52897_25000 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_17 : (Function.update (topLoS8) 1 cA1_52897_25000 (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nhi_17 : (Function.update (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 2 cA2_52897_25000) 0 cA0_68_25 (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_18 : (Function.update (Function.update (topLoS8) 1 cA1_52897_25000) 0 cA0_68_25 (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem nhi_18 : (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 2 cA2_52897_25000 (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_19 : (Function.update (topLoS8) 1 cA1_52897_25000 (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem nhi_19 : (Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500) 2 cA2_52897_25000 (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem nlo_20 : (Function.update (topLoS8) 1 cA1_52897_25000 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_20 : (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_21 : (topLoS8 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_21 : (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500 (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_22 : (Function.update (topLoS8) 2 cA2_27897_12500 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_22 : (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_58691_25000 (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_23 : (Function.update (topLoS8) 2 cA2_27897_12500 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nhi_23 : (Function.update (topHiS8) 1 cA1_27897_12500 (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_24 : (topLoS8 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_24 : (Function.update (topHiS8) 1 cA1_27897_12500 (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_25 : (Function.update (topLoS8) 1 cA1_27897_12500 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_25 : (Function.update (Function.update (topHiS8) 2 cA2_27897_12500) 1 cA1_58691_25000 (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nlo_26 : (Function.update (topLoS8) 1 cA1_27897_12500 (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem nhi_26 : (Function.update (topHiS8) 2 cA2_27897_12500 (1 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_27 : (Function.update (topLoS8) 1 cA1_27897_12500 (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_27 : (topHiS8 (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem nlo_28 : (topLoS8 (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem nhi_28 : (topHiS8 (1 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide

/-- leaf table: endpoints are the EXACT tree-path expressions, so every
`Cover.leaf` obligation closes by `rfl` (identical terms). -/
def rowsS8 : Fin 30 → LeafRow 3 Unit := fun j => match (j : ℕ) with
  | 0 => { boxLo := topLoS8, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_202897_100000) 2 cA2_202897_100000) 0 cA0_2683_1000, aux := () }
  | 1 => { boxLo := Function.update (topLoS8) 2 cA2_202897_100000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_202897_100000) 2 cA2_102897_50000) 0 cA0_2683_1000, aux := () }
  | 2 => { boxLo := Function.update (topLoS8) 1 cA1_202897_100000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_2683_1000, aux := () }
  | 3 => { boxLo := Function.update (topLoS8) 0 cA0_2683_1000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_202897_100000) 2 cA2_102897_50000) 0 cA0_68_25, aux := () }
  | 4 => { boxLo := Function.update (Function.update (topLoS8) 0 cA0_2683_1000) 1 cA1_202897_100000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_68_25, aux := () }
  | 5 => { boxLo := Function.update (topLoS8) 2 cA2_102897_50000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_52897_25000) 0 cA0_68_25, aux := () }
  | 6 => { boxLo := Function.update (topLoS8) 1 cA1_102897_50000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_102897_50000) 0 cA0_68_25, aux := () }
  | 7 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_102897_50000) 2 cA2_102897_50000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_52897_25000) 0 cA0_68_25, aux := () }
  | 8 => { boxLo := Function.update (topLoS8) 0 cA0_68_25, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_202897_100000) 2 cA2_102897_50000) 0 cA0_139_50, aux := () }
  | 9 => { boxLo := Function.update (Function.update (topLoS8) 0 cA0_68_25) 1 cA1_202897_100000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_102897_50000) 0 cA0_139_50, aux := () }
  | 10 => { boxLo := Function.update (topLoS8) 0 cA0_139_50, boxHi := Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_102897_50000, aux := () }
  | 11 => { boxLo := Function.update (Function.update (topLoS8) 0 cA0_68_25) 2 cA2_102897_50000, boxHi := Function.update (Function.update (topHiS8) 1 cA1_102897_50000) 2 cA2_52897_25000, aux := () }
  | 12 => { boxLo := Function.update (Function.update (topLoS8) 0 cA0_68_25) 1 cA1_102897_50000, boxHi := Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_102897_50000, aux := () }
  | 13 => { boxLo := Function.update (Function.update (Function.update (topLoS8) 0 cA0_68_25) 1 cA1_102897_50000) 2 cA2_102897_50000, boxHi := Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_52897_25000, aux := () }
  | 14 => { boxLo := Function.update (topLoS8) 2 cA2_52897_25000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_108691_50000) 0 cA0_68_25, aux := () }
  | 15 => { boxLo := Function.update (topLoS8) 2 cA2_108691_50000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_27897_12500) 0 cA0_68_25, aux := () }
  | 16 => { boxLo := Function.update (Function.update (topLoS8) 2 cA2_52897_25000) 0 cA0_68_25, boxHi := Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_108691_50000, aux := () }
  | 17 => { boxLo := Function.update (Function.update (topLoS8) 2 cA2_108691_50000) 0 cA0_68_25, boxHi := Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_27897_12500, aux := () }
  | 18 => { boxLo := Function.update (topLoS8) 1 cA1_52897_25000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_108691_50000) 2 cA2_52897_25000) 0 cA0_68_25, aux := () }
  | 19 => { boxLo := Function.update (topLoS8) 1 cA1_108691_50000, boxHi := Function.update (Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_52897_25000) 0 cA0_68_25, aux := () }
  | 20 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_52897_25000) 0 cA0_68_25, boxHi := Function.update (Function.update (topHiS8) 1 cA1_108691_50000) 2 cA2_52897_25000, aux := () }
  | 21 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_108691_50000) 0 cA0_68_25, boxHi := Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_52897_25000, aux := () }
  | 22 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_52897_25000) 2 cA2_52897_25000, boxHi := Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_27897_12500, aux := () }
  | 23 => { boxLo := Function.update (topLoS8) 2 cA2_27897_12500, boxHi := Function.update (Function.update (topHiS8) 1 cA1_52897_25000) 2 cA2_58691_25000, aux := () }
  | 24 => { boxLo := Function.update (Function.update (topLoS8) 2 cA2_27897_12500) 1 cA1_52897_25000, boxHi := Function.update (Function.update (topHiS8) 1 cA1_27897_12500) 2 cA2_58691_25000, aux := () }
  | 25 => { boxLo := Function.update (topLoS8) 2 cA2_58691_25000, boxHi := Function.update (topHiS8) 1 cA1_27897_12500, aux := () }
  | 26 => { boxLo := Function.update (topLoS8) 1 cA1_27897_12500, boxHi := Function.update (Function.update (topHiS8) 2 cA2_52897_25000) 1 cA1_58691_25000, aux := () }
  | 27 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_27897_12500) 2 cA2_52897_25000, boxHi := Function.update (Function.update (topHiS8) 2 cA2_27897_12500) 1 cA1_58691_25000, aux := () }
  | 28 => { boxLo := Function.update (topLoS8) 1 cA1_58691_25000, boxHi := Function.update (topHiS8) 2 cA2_27897_12500, aux := () }
  | 29 => { boxLo := Function.update (Function.update (topLoS8) 1 cA1_27897_12500) 2 cA2_27897_12500, boxHi := topHiS8, aux := () }
  | _ => { boxLo := topLoS8, boxHi := topHiS8, aux := () }

def leafPassS8 : Fin 30 → Bool := fun _ => true

end Kepler.NliKit.BoxTreeSqrt8

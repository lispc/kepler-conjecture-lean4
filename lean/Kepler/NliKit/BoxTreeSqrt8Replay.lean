/-
Kepler.NliKit.BoxTreeSqrt8Replay — P-A regression replay assembly for sqrt8
(lane nlikit-boxtree-impl-w1; machine-generated, PYTHONHASHSEED=0).
cover_sound + hsound over the sharded leaf witnesses; statement of the
hcore is the verbatim hypothesis shape of the original bridge.
-/
import Kepler.NliKit.BoxTreeS8Rows
import Kepler.NliKit.BoxTreeSqrt8S0
import Kepler.NliKit.BoxTreeSqrt8S1
import Kepler.NliKit.BoxTreeSqrt8S2
import Kepler.NliKit.BoxTreeSqrt8S3
import Kepler.NliKit.BoxTreeSqrt8S4
import Kepler.NliKit.BoxTreeSqrt8S5
import Kepler.NliKit.BoxTreeSqrt8S6
import Kepler.NliKit.BoxTreeSqrt8S7
import Kepler.NliKit.BoxTreeSqrt8S8
import Kepler.NliKit.BoxTreeSqrt8S9
import Kepler.NliKit.BoxTreeSqrt8S10
import Kepler.NliKit.BoxTreeSqrt8S11
import Kepler.NliKit.BoxTreeSqrt8S12
import Kepler.NliKit.BoxTreeSqrt8S13
import Kepler.NliKit.BoxTreeSqrt8S14
import Kepler.NliKit.BoxTreeSqrt8S15

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree
open Kepler.Text

theorem vTL0 : (topLoS8 (0 : Fin 3)).value ≤ (2.6508:ℝ) := by
  have hv : (topLoS8 (0 : Fin 3)) = (⟨(40 : ℤ), 2914585422908, 2914585422908⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTL1 : (topLoS8 (1 : Fin 3)).value ≤ (2:ℝ) := by
  have hv : (topLoS8 (1 : Fin 3)) = (⟨(40 : ℤ), 2199023255552, 2199023255552⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTL2 : (topLoS8 (2 : Fin 3)).value ≤ (2:ℝ) := by
  have hv : (topLoS8 (2 : Fin 3)) = (⟨(40 : ℤ), 2199023255552, 2199023255552⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTH0 : (Real.sqrt 8 : ℝ) ≤ (topHiS8 (0 : Fin 3)).value := by
  have hv : (topHiS8 (0 : Fin 3)) = (⟨(40 : ℤ), 3109888511976, 3109888511976⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num
theorem vTH1 : (2.46352:ℝ) ≤ (topHiS8 (1 : Fin 3)).value := by
  have hv : (topHiS8 (1 : Fin 3)) = (⟨(40 : ℤ), 2708668885259, 2708668885259⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTH2 : (2.46352:ℝ) ≤ (topHiS8 (2 : Fin 3)).value := by
  have hv : (topHiS8 (2 : Fin 3)) = (⟨(40 : ℤ), 2708668885259, 2708668885259⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num

theorem hsoundS8 : ∀ j : Fin 30, leafPassS8 j = true →
    ∀ x ∈ rowBox (rowsS8 j), PS8 x := by
  intro j _ x hx
  fin_cases j <;> first
    | exact leaf_00_s8_cell00 x hx
    | exact leaf_01_s8_cell01 x hx
    | exact leaf_02_s8_cell02 x hx
    | exact leaf_03_s8_cell03 x hx
    | exact leaf_04_s8_cell04 x hx
    | exact leaf_05_s8_cell05 x hx
    | exact leaf_06_s8_cell06 x hx
    | exact leaf_07_s8_cell07 x hx
    | exact leaf_08_s8_cell08 x hx
    | exact leaf_09_s8_cell09 x hx
    | exact leaf_10_s8_cell10 x hx
    | exact leaf_11_s8_cell11 x hx
    | exact leaf_12_s8_cell12 x hx
    | exact leaf_13_s8_cell13 x hx
    | exact leaf_14_s8_cell14 x hx
    | exact leaf_15_s8_cell15 x hx
    | exact leaf_16_s8_cell16 x hx
    | exact leaf_17_s8_cell17 x hx
    | exact leaf_18_s8_cell18 x hx
    | exact leaf_19_absurd x hx
    | exact leaf_20_s8_cell20 x hx
    | exact leaf_21_absurd x hx
    | exact leaf_22_s8_cell22 x hx
    | exact leaf_23_s8_cell23 x hx
    | exact leaf_24_s8_cell24 x hx
    | exact leaf_25_s8_cell25 x hx
    | exact leaf_26_absurd x hx
    | exact leaf_27_s8_cell27 x hx
    | exact leaf_28_absurd x hx
    | exact leaf_29_s8_cell29 x hx

theorem coverS8 : Cover PS8 rowsS8 leafPassS8 topLoS8 topHiS8 :=
Cover.node (1 : Fin 3) cA1_27897_12500 (⟨by rw [nlo_28, vB40_2199023255552, cA1_27897_12500_eq, vB40_2453846070405]; linarith, by rw [nhi_28, vB40_2708668885259, cA1_27897_12500_eq, vB40_2453846070405]; linarith⟩)
 (Cover.node (2 : Fin 3) cA2_27897_12500 (⟨by rw [nlo_24, vB40_2199023255552, cA2_27897_12500_eq, vB40_2453846070405]; linarith, by rw [nhi_24, vB40_2708668885259, cA2_27897_12500_eq, vB40_2453846070405]; linarith⟩)
  (Cover.node (1 : Fin 3) cA1_52897_25000 (⟨by rw [nlo_21, vB40_2199023255552, cA1_52897_25000_eq, vB40_2326434662978]; linarith, by rw [nhi_21, vB40_2453846070405, cA1_52897_25000_eq, vB40_2326434662978]; linarith⟩)
   (Cover.node (2 : Fin 3) cA2_52897_25000 (⟨by rw [nlo_16, vB40_2199023255552, cA2_52897_25000_eq, vB40_2326434662978]; linarith, by rw [nhi_16, vB40_2453846070405, cA2_52897_25000_eq, vB40_2326434662978]; linarith⟩)
    (Cover.node (0 : Fin 3) cA0_68_25 (⟨by rw [nlo_12, vB40_2914585422908, cA0_68_25_eq, vB40_2990671627550]; linarith, by rw [nhi_12, vB40_3109888511976, cA0_68_25_eq, vB40_2990671627550]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_102897_50000 (⟨by rw [nlo_6, vB40_2199023255552, cA1_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_6, vB40_2326434662978, cA1_102897_50000_eq, vB40_2262728959265]; linarith⟩)
      (Cover.node (2 : Fin 3) cA2_102897_50000 (⟨by rw [nlo_4, vB40_2199023255552, cA2_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_4, vB40_2326434662978, cA2_102897_50000_eq, vB40_2262728959265]; linarith⟩)
       (Cover.node (0 : Fin 3) cA0_2683_1000 (⟨by rw [nlo_3, vB40_2914585422908, cA0_2683_1000_eq, vB40_2949989697323]; linarith, by rw [nhi_3, vB40_2990671627550, cA0_2683_1000_eq, vB40_2949989697323]; linarith⟩)
        (Cover.node (1 : Fin 3) cA1_202897_100000 (⟨by rw [nlo_1, vB40_2199023255552, cA1_202897_100000_eq, vB40_2230876107408]; linarith, by rw [nhi_1, vB40_2262728959265, cA1_202897_100000_eq, vB40_2230876107408]; linarith⟩)
         (Cover.node (2 : Fin 3) cA2_202897_100000 (⟨by rw [nlo_0, vB40_2199023255552, cA2_202897_100000_eq, vB40_2230876107408]; linarith, by rw [nhi_0, vB40_2262728959265, cA2_202897_100000_eq, vB40_2230876107408]; linarith⟩)
          (Cover.leaf (0 : Fin 30) (by decide) (by decide) rfl)
          (Cover.leaf (1 : Fin 30) (by decide) (by decide) rfl))
         (Cover.leaf (2 : Fin 30) (by decide) (by decide) rfl))
        (Cover.node (1 : Fin 3) cA1_202897_100000 (⟨by rw [nlo_2, vB40_2199023255552, cA1_202897_100000_eq, vB40_2230876107408]; linarith, by rw [nhi_2, vB40_2262728959265, cA1_202897_100000_eq, vB40_2230876107408]; linarith⟩)
         (Cover.leaf (3 : Fin 30) (by decide) (by decide) rfl)
         (Cover.leaf (4 : Fin 30) (by decide) (by decide) rfl)))
       (Cover.leaf (5 : Fin 30) (by decide) (by decide) rfl))
      (Cover.node (2 : Fin 3) cA2_102897_50000 (⟨by rw [nlo_5, vB40_2199023255552, cA2_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_5, vB40_2326434662978, cA2_102897_50000_eq, vB40_2262728959265]; linarith⟩)
       (Cover.leaf (6 : Fin 30) (by decide) (by decide) rfl)
       (Cover.leaf (7 : Fin 30) (by decide) (by decide) rfl)))
     (Cover.node (1 : Fin 3) cA1_102897_50000 (⟨by rw [nlo_11, vB40_2199023255552, cA1_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_11, vB40_2326434662978, cA1_102897_50000_eq, vB40_2262728959265]; linarith⟩)
      (Cover.node (2 : Fin 3) cA2_102897_50000 (⟨by rw [nlo_9, vB40_2199023255552, cA2_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_9, vB40_2326434662978, cA2_102897_50000_eq, vB40_2262728959265]; linarith⟩)
       (Cover.node (0 : Fin 3) cA0_139_50 (⟨by rw [nlo_8, vB40_2990671627550, cA0_139_50_eq, vB40_3056642325217]; linarith, by rw [nhi_8, vB40_3109888511976, cA0_139_50_eq, vB40_3056642325217]; linarith⟩)
        (Cover.node (1 : Fin 3) cA1_202897_100000 (⟨by rw [nlo_7, vB40_2199023255552, cA1_202897_100000_eq, vB40_2230876107408]; linarith, by rw [nhi_7, vB40_2262728959265, cA1_202897_100000_eq, vB40_2230876107408]; linarith⟩)
         (Cover.leaf (8 : Fin 30) (by decide) (by decide) rfl)
         (Cover.leaf (9 : Fin 30) (by decide) (by decide) rfl))
        (Cover.leaf (10 : Fin 30) (by decide) (by decide) rfl))
       (Cover.leaf (11 : Fin 30) (by decide) (by decide) rfl))
      (Cover.node (2 : Fin 3) cA2_102897_50000 (⟨by rw [nlo_10, vB40_2199023255552, cA2_102897_50000_eq, vB40_2262728959265]; linarith, by rw [nhi_10, vB40_2326434662978, cA2_102897_50000_eq, vB40_2262728959265]; linarith⟩)
       (Cover.leaf (12 : Fin 30) (by decide) (by decide) rfl)
       (Cover.leaf (13 : Fin 30) (by decide) (by decide) rfl))))
    (Cover.node (0 : Fin 3) cA0_68_25 (⟨by rw [nlo_15, vB40_2914585422908, cA0_68_25_eq, vB40_2990671627550]; linarith, by rw [nhi_15, vB40_3109888511976, cA0_68_25_eq, vB40_2990671627550]; linarith⟩)
     (Cover.node (2 : Fin 3) cA2_108691_50000 (⟨by rw [nlo_13, vB40_2326434662978, cA2_108691_50000_eq, vB40_2390140366692]; linarith, by rw [nhi_13, vB40_2453846070405, cA2_108691_50000_eq, vB40_2390140366692]; linarith⟩)
      (Cover.leaf (14 : Fin 30) (by decide) (by decide) rfl)
      (Cover.leaf (15 : Fin 30) (by decide) (by decide) rfl))
     (Cover.node (2 : Fin 3) cA2_108691_50000 (⟨by rw [nlo_14, vB40_2326434662978, cA2_108691_50000_eq, vB40_2390140366692]; linarith, by rw [nhi_14, vB40_2453846070405, cA2_108691_50000_eq, vB40_2390140366692]; linarith⟩)
      (Cover.leaf (16 : Fin 30) (by decide) (by decide) rfl)
      (Cover.leaf (17 : Fin 30) (by decide) (by decide) rfl))))
   (Cover.node (2 : Fin 3) cA2_52897_25000 (⟨by rw [nlo_20, vB40_2199023255552, cA2_52897_25000_eq, vB40_2326434662978]; linarith, by rw [nhi_20, vB40_2453846070405, cA2_52897_25000_eq, vB40_2326434662978]; linarith⟩)
    (Cover.node (0 : Fin 3) cA0_68_25 (⟨by rw [nlo_19, vB40_2914585422908, cA0_68_25_eq, vB40_2990671627550]; linarith, by rw [nhi_19, vB40_3109888511976, cA0_68_25_eq, vB40_2990671627550]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_108691_50000 (⟨by rw [nlo_17, vB40_2326434662978, cA1_108691_50000_eq, vB40_2390140366692]; linarith, by rw [nhi_17, vB40_2453846070405, cA1_108691_50000_eq, vB40_2390140366692]; linarith⟩)
      (Cover.leaf (18 : Fin 30) (by decide) (by decide) rfl)
      (Cover.leaf (19 : Fin 30) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_108691_50000 (⟨by rw [nlo_18, vB40_2326434662978, cA1_108691_50000_eq, vB40_2390140366692]; linarith, by rw [nhi_18, vB40_2453846070405, cA1_108691_50000_eq, vB40_2390140366692]; linarith⟩)
      (Cover.leaf (20 : Fin 30) (by decide) (by decide) rfl)
      (Cover.leaf (21 : Fin 30) (by decide) (by decide) rfl)))
    (Cover.leaf (22 : Fin 30) (by decide) (by decide) rfl)))
  (Cover.node (2 : Fin 3) cA2_58691_25000 (⟨by rw [nlo_23, vB40_2453846070405, cA2_58691_25000_eq, vB40_2581257477832]; linarith, by rw [nhi_23, vB40_2708668885259, cA2_58691_25000_eq, vB40_2581257477832]; linarith⟩)
   (Cover.node (1 : Fin 3) cA1_52897_25000 (⟨by rw [nlo_22, vB40_2199023255552, cA1_52897_25000_eq, vB40_2326434662978]; linarith, by rw [nhi_22, vB40_2453846070405, cA1_52897_25000_eq, vB40_2326434662978]; linarith⟩)
    (Cover.leaf (23 : Fin 30) (by decide) (by decide) rfl)
    (Cover.leaf (24 : Fin 30) (by decide) (by decide) rfl))
   (Cover.leaf (25 : Fin 30) (by decide) (by decide) rfl)))
 (Cover.node (2 : Fin 3) cA2_27897_12500 (⟨by rw [nlo_27, vB40_2199023255552, cA2_27897_12500_eq, vB40_2453846070405]; linarith, by rw [nhi_27, vB40_2708668885259, cA2_27897_12500_eq, vB40_2453846070405]; linarith⟩)
  (Cover.node (1 : Fin 3) cA1_58691_25000 (⟨by rw [nlo_26, vB40_2453846070405, cA1_58691_25000_eq, vB40_2581257477832]; linarith, by rw [nhi_26, vB40_2708668885259, cA1_58691_25000_eq, vB40_2581257477832]; linarith⟩)
   (Cover.node (2 : Fin 3) cA2_52897_25000 (⟨by rw [nlo_25, vB40_2199023255552, cA2_52897_25000_eq, vB40_2326434662978]; linarith, by rw [nhi_25, vB40_2453846070405, cA2_52897_25000_eq, vB40_2326434662978]; linarith⟩)
    (Cover.leaf (26 : Fin 30) (by decide) (by decide) rfl)
    (Cover.leaf (27 : Fin 30) (by decide) (by decide) rfl))
   (Cover.leaf (28 : Fin 30) (by decide) (by decide) rfl))
  (Cover.leaf (29 : Fin 30) (by decide) (by decide) rfl))

/-- R2: s8_half, replayed through the tree.  Statement = s8_half
verbatim (NliSqrt8.lean:3822). -/
theorem s8_half_cover {y4 y5 y6 : ℝ} (h4 : (2:ℝ) * hplus ≤ y4)
    (h4' : y4 ≤ Real.sqrt 8) (h5 : (2:ℝ) ≤ y5) (h5' : y5 ≤ (2:ℝ) * hminus)
    (h6 : (2:ℝ) ≤ y6) (h6' : y6 ≤ (2:ℝ) * hminus) (hy56 : y5 ≤ y6)
    (hdlt : (0:ℝ) ≤ Kepler.Text.deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    (0:ℝ) < Kepler.NliBanks11.c3Main y4 y5 y6 := by
  refine cover_sound hsoundS8 coverS8
    (fun i => if (i : ℕ) = 0 then y4 else if (i : ℕ) = 1 then y5 else y6) ?_
    h4 h4' h5 h5' h6 h6' hy56 hdlt
  intro i
  fin_cases i
  · show (topLoS8 (0 : Fin 3)).value ≤ y4 ∧ y4 ≤ (topHiS8 (0 : Fin 3)).value
    exact ⟨by linarith [vTL0, s8hp, h4], by linarith [vTH0, h4']⟩
  · show (topLoS8 (1 : Fin 3)).value ≤ y5 ∧ y5 ≤ (topHiS8 (1 : Fin 3)).value
    exact ⟨by linarith [vTL1, h5],
      by linarith [vTH1, Kepler.NliBanks17.nb17_two_hminus_bounds.2, h5']⟩
  · show (topLoS8 (2 : Fin 3)).value ≤ y6 ∧ y6 ≤ (topHiS8 (2 : Fin 3)).value
    exact ⟨by linarith [vTL2, h6],
      by linarith [vTH2, Kepler.NliBanks17.nb17_two_hminus_bounds.2, h6']⟩

/-- R2 assembly: s8_bank's skeleton verbatim (NliSqrt8.lean:4029-4041),
with s8_half → s8_half_cover. -/
theorem s8_bank_cover : Kepler.Text.bank_QZECFICwt0sqrt8 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  by_cases hdlt : (0:ℝ) ≤ Kepler.Text.deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2
  · left
    rw [Kepler.NliBanks11.nb11_c3_indep]
    by_cases hy56 : y5 ≤ y6
    · exact s8_half_cover h4 h4' h5 h5' h6 h6' hy56 hdlt
    · rw [Kepler.Text.NliSqrt8.s8_c3_symm (le_trans (by norm_num [Kepler.Text.hplus] : (0:ℝ) ≤ 2 * hplus) h4)
        (le_trans (by norm_num : (0:ℝ) ≤ (2:ℝ)) h5)
        (le_trans (by norm_num : (0:ℝ) ≤ (2:ℝ)) h6)]
      exact s8_half_cover h4 h4' h6 h6' h5 h5' (by linarith)
        (by rw [Kepler.NliBanks20.dlt4_eq]; exact hdlt)
  · right
    exact Kepler.Text.NliSqrt8.s8_eta_dlt_neg h4 h4' h5 h5' h6 h6' (lt_of_not_ge hdlt)


#print axioms s8_half_cover
#print axioms s8_bank_cover

end Kepler.NliKit.BoxTreeSqrt8

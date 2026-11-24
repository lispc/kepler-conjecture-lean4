/-
Kepler.NliKit.BoxTreeWt2AReplay — P-A regression replay assembly for wt2A
(lane nlikit-boxtree-impl-w1; machine-generated, PYTHONHASHSEED=0).
cover_sound + hsound over the sharded leaf witnesses; statement of the
hcore is the verbatim hypothesis shape of the original bridge.
-/
import Kepler.NliKit.BoxTreeWt2ARows
import Kepler.NliKit.BoxTreeWt2AS0
import Kepler.NliKit.BoxTreeWt2AS1
import Kepler.NliKit.BoxTreeWt2AS2
import Kepler.NliKit.BoxTreeWt2AS3
import Kepler.NliKit.BoxTreeWt2AS4

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem vTL0 : (topLoWt2A (0 : Fin 3)).value ≤ (2.4635:ℝ) := by
  have hv : (topLoWt2A (0 : Fin 3)) = (⟨(40 : ℤ), 2708646895026, 2708646895026⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTL1 : (topLoWt2A (1 : Fin 3)).value ≤ (2.4635:ℝ) := by
  have hv : (topLoWt2A (1 : Fin 3)) = (⟨(40 : ℤ), 2708646895026, 2708646895026⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTL2 : (topLoWt2A (2 : Fin 3)).value ≤ (2:ℝ) := by
  have hv : (topLoWt2A (2 : Fin 3)) = (⟨(40 : ℤ), 2199023255552, 2199023255552⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num
theorem vTH0 : (Real.sqrt 8 : ℝ) ≤ (topHiWt2A (0 : Fin 3)).value := by
  have hv : (topHiWt2A (0 : Fin 3)) = (⟨(40 : ℤ), 3109888511976, 3109888511976⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num
theorem vTH1 : (Real.sqrt 8 : ℝ) ≤ (topHiWt2A (1 : Fin 3)).value := by
  have hv : (topHiWt2A (1 : Fin 3)) = (⟨(40 : ℤ), 3109888511976, 3109888511976⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num
theorem vTH2 : (2.46352:ℝ) ≤ (topHiWt2A (2 : Fin 3)).value := by
  have hv : (topHiWt2A (2 : Fin 3)) = (⟨(40 : ℤ), 2708668885259, 2708668885259⟩ : DC) := by decide
  rw [hv]
  simp [DC.value, kNat40]
  norm_num

theorem hsoundWt2A : ∀ j : Fin 62, leafPassWt2A j = true →
    ∀ x ∈ rowBox (rowsWt2A j), PWt2A x := by
  intro j _ x hx
  fin_cases j <;> first
    | exact leaf_00_cell10_core x hx
    | exact leaf_01_cell15_core x hx
    | exact leaf_02_cell05_core x hx
    | exact leaf_03_cell25_core x hx
    | exact leaf_04_cell09_core x hx
    | exact leaf_05_cell14_core x hx
    | exact leaf_06_cell07_core x hx
    | exact leaf_07_cell26_core x hx
    | exact leaf_08_cell08_core x hx
    | exact leaf_09_cell13_core x hx
    | exact leaf_10_cell06_core x hx
    | exact leaf_11_cell27_core x hx
    | exact leaf_12_cell03_core x hx
    | exact leaf_13_cell12_core x hx
    | exact leaf_14_cell04_core x hx
    | exact leaf_15_cell28_core x hx
    | exact leaf_16_cell11_core x hx
    | exact leaf_17_cell16_core x hx
    | exact leaf_18_cell19_core x hx
    | exact leaf_19_cell21_core x hx
    | exact leaf_20_cell02_core x hx
    | exact leaf_21_cell01_core x hx
    | exact leaf_22_cell24_core x hx
    | exact leaf_23_cell17_core x hx
    | exact leaf_24_cell20_core x hx
    | exact leaf_25_cell18_core x hx
    | exact leaf_26_cell29_vac x hx
    | exact leaf_27_cell22_core x hx
    | exact leaf_28_cell_vac_demo x hx
    | exact leaf_29_cell23_core x hx
    | exact leaf_30_cell31_vac x hx
    | exact leaf_31_cell00_core x hx
    | exact leaf_32_cell33_core x hx
    | exact leaf_33_cell38_core x hx
    | exact leaf_34_cell39_core x hx
    | exact leaf_35_cell45_core x hx
    | exact leaf_36_cell46_core x hx
    | exact leaf_37_cell32_core x hx
    | exact leaf_38_cell40_core x hx
    | exact leaf_39_cell41_core x hx
    | exact leaf_40_cell47_core x hx
    | exact leaf_41_cell51_vac x hx
    | exact leaf_42_cell34_core x hx
    | exact leaf_43_cell37_core x hx
    | exact leaf_44_cell42_core x hx
    | exact leaf_45_cell43_core x hx
    | exact leaf_46_cell35_core x hx
    | exact leaf_47_cell36_core x hx
    | exact leaf_48_cell49_vac x hx
    | exact leaf_49_cell44_core x hx
    | exact leaf_50_cell50_vac x hx
    | exact leaf_51_cell48_vac x hx
    | exact leaf_52_cell54_core x hx
    | exact leaf_53_cell55_core x hx
    | exact leaf_54_cell56_core x hx
    | exact leaf_55_cell57_core x hx
    | exact leaf_56_cell52_core x hx
    | exact leaf_57_cell53_core x hx
    | exact leaf_58_cell58_vac x hx
    | exact leaf_59_cell59_vac x hx
    | exact leaf_60_cell61_core x hx
    | exact leaf_61_cell60_core x hx

theorem coverWt2A : Cover PWt2A rowsWt2A leafPassWt2A topLoWt2A topHiWt2A :=
Cover.node (2 : Fin 3) cA2_1029_500 (⟨by rw [nlo_60, vB40_2199023255552, cA2_1029_500_eq, vB40_2262794929963]; linarith, by rw [nhi_60, vB40_2708668885259, cA2_1029_500_eq, vB40_2262794929963]; linarith⟩)
 (Cover.node (0 : Fin 3) cA0_63_25 (⟨by rw [nlo_30, vB40_2708646895026, cA0_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_30, vB40_3109888511976, cA0_63_25_eq, vB40_2770769301995]; linarith⟩)
  (Cover.node (0 : Fin 3) cA0_9967_4000 (⟨by rw [nlo_14, vB40_2708646895026, cA0_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_14, vB40_2770769301995, cA0_9967_4000_eq, vB40_2739708098510]; linarith⟩)
   (Cover.node (0 : Fin 3) cA0_19821_8000 (⟨by rw [nlo_6, vB40_2708646895026, cA0_19821_8000_eq, vB40_2724177496768]; linarith, by rw [nhi_6, vB40_2739708098510, cA0_19821_8000_eq, vB40_2724177496768]; linarith⟩)
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_2, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_2, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_0, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_0, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (0 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (1 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_1, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_1, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (2 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (3 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_5, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_5, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_3, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_3, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (4 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (5 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_4, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_4, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (6 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (7 : Fin 62) (by decide) (by decide) rfl))))
   (Cover.node (0 : Fin 3) cA0_20047_8000 (⟨by rw [nlo_13, vB40_2739708098510, cA0_20047_8000_eq, vB40_2755238700253]; linarith, by rw [nhi_13, vB40_2770769301995, cA0_20047_8000_eq, vB40_2755238700253]; linarith⟩)
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_9, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_9, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_7, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_7, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (8 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (9 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_8, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_8, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (10 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (11 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_12, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_12, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_10, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_10, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (12 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (13 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_11, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_11, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (14 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (15 : Fin 62) (by decide) (by decide) rfl)))))
  (Cover.node (0 : Fin 3) cA0_129855339_50000000 (⟨by rw [nlo_29, vB40_2770769301995, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith, by rw [nhi_29, vB40_3109888511976, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith⟩)
   (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_20, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_20, vB40_3109888511976, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
    (Cover.node (0 : Fin 3) cA0_255855339_100000000 (⟨by rw [nlo_17, vB40_2770769301995, cA0_255855339_100000000_eq, vB40_2813159202590]; linarith, by rw [nhi_17, vB40_2855549103185, cA0_255855339_100000000_eq, vB40_2813159202590]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_19821_8000 (⟨by rw [nlo_15, vB40_2708646895026, cA1_19821_8000_eq, vB40_2724177496768]; linarith, by rw [nhi_15, vB40_2739708098510, cA1_19821_8000_eq, vB40_2724177496768]; linarith⟩)
      (Cover.leaf (16 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (17 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_19821_8000 (⟨by rw [nlo_16, vB40_2708646895026, cA1_19821_8000_eq, vB40_2724177496768]; linarith, by rw [nhi_16, vB40_2739708098510, cA1_19821_8000_eq, vB40_2724177496768]; linarith⟩)
      (Cover.leaf (18 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (19 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_19, vB40_2739708098510, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_19, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.leaf (20 : Fin 62) (by decide) (by decide) rfl)
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_18, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_18, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (21 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (22 : Fin 62) (by decide) (by decide) rfl))))
   (Cover.node (0 : Fin 3) cA0_66855339_25000000 (⟨by rw [nlo_28, vB40_2855549103185, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_28, vB40_3109888511976, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
    (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_23, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_23, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_21, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_21, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (23 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (24 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_22, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_22, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (25 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (26 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_27, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_27, vB40_3109888511976, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
     (Cover.node (0 : Fin 3) cA0_137566017_50000000 (⟨by rw [nlo_24, vB40_2940328904376, cA0_137566017_50000000_eq, vB40_3025108705566]; linarith, by rw [nhi_24, vB40_3109888511976, cA0_137566017_50000000_eq, vB40_3025108705566]; linarith⟩)
      (Cover.leaf (27 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (28 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_26, vB40_2739708098510, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_26, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.node (0 : Fin 3) cA0_137566017_50000000 (⟨by rw [nlo_25, vB40_2940328904376, cA0_137566017_50000000_eq, vB40_3025108705566]; linarith, by rw [nhi_25, vB40_3109888511976, cA0_137566017_50000000_eq, vB40_3025108705566]; linarith⟩)
       (Cover.leaf (29 : Fin 62) (by decide) (by decide) rfl)
       (Cover.leaf (30 : Fin 62) (by decide) (by decide) rfl))
      (Cover.leaf (31 : Fin 62) (by decide) (by decide) rfl))))))
 (Cover.node (2 : Fin 3) cA2_1087_500 (⟨by rw [nlo_59, vB40_2262794929963, cA2_1087_500_eq, vB40_2390338278785]; linarith, by rw [nhi_59, vB40_2708668885259, cA2_1087_500_eq, vB40_2390338278785]; linarith⟩)
  (Cover.node (0 : Fin 3) cA0_63_25 (⟨by rw [nlo_49, vB40_2708646895026, cA0_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_49, vB40_3109888511976, cA0_63_25_eq, vB40_2770769301995]; linarith⟩)
   (Cover.node (0 : Fin 3) cA0_9967_4000 (⟨by rw [nlo_39, vB40_2708646895026, cA0_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_39, vB40_2770769301995, cA0_9967_4000_eq, vB40_2739708098510]; linarith⟩)
    (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_34, vB40_2708646895026, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_34, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_32, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_32, vB40_2940328904376, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (32 : Fin 62) (by decide) (by decide) rfl)
      (Cover.node (0 : Fin 3) cA0_19821_8000 (⟨by rw [nlo_31, vB40_2708646895026, cA0_19821_8000_eq, vB40_2724177496768]; linarith, by rw [nhi_31, vB40_2739708098510, cA0_19821_8000_eq, vB40_2724177496768]; linarith⟩)
       (Cover.leaf (33 : Fin 62) (by decide) (by decide) rfl)
       (Cover.leaf (34 : Fin 62) (by decide) (by decide) rfl)))
     (Cover.node (0 : Fin 3) cA0_19821_8000 (⟨by rw [nlo_33, vB40_2708646895026, cA0_19821_8000_eq, vB40_2724177496768]; linarith, by rw [nhi_33, vB40_2739708098510, cA0_19821_8000_eq, vB40_2724177496768]; linarith⟩)
      (Cover.leaf (35 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (36 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_38, vB40_2708646895026, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_38, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_36, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_36, vB40_2940328904376, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (37 : Fin 62) (by decide) (by decide) rfl)
      (Cover.node (0 : Fin 3) cA0_20047_8000 (⟨by rw [nlo_35, vB40_2739708098510, cA0_20047_8000_eq, vB40_2755238700253]; linarith, by rw [nhi_35, vB40_2770769301995, cA0_20047_8000_eq, vB40_2755238700253]; linarith⟩)
       (Cover.leaf (38 : Fin 62) (by decide) (by decide) rfl)
       (Cover.leaf (39 : Fin 62) (by decide) (by decide) rfl)))
     (Cover.node (0 : Fin 3) cA0_20047_8000 (⟨by rw [nlo_37, vB40_2739708098510, cA0_20047_8000_eq, vB40_2755238700253]; linarith, by rw [nhi_37, vB40_2770769301995, cA0_20047_8000_eq, vB40_2755238700253]; linarith⟩)
      (Cover.leaf (40 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (41 : Fin 62) (by decide) (by decide) rfl))))
   (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_48, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_48, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
    (Cover.node (0 : Fin 3) cA0_129855339_50000000 (⟨by rw [nlo_43, vB40_2770769301995, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith, by rw [nhi_43, vB40_3109888511976, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_40, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_40, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
      (Cover.leaf (42 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (43 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (0 : Fin 3) cA0_66855339_25000000 (⟨by rw [nlo_42, vB40_2855549103185, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_42, vB40_3109888511976, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.node (1 : Fin 3) cA1_9967_4000 (⟨by rw [nlo_41, vB40_2708646895026, cA1_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_41, vB40_2770769301995, cA1_9967_4000_eq, vB40_2739708098510]; linarith⟩)
       (Cover.leaf (44 : Fin 62) (by decide) (by decide) rfl)
       (Cover.leaf (45 : Fin 62) (by decide) (by decide) rfl))
      (Cover.leaf (46 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (0 : Fin 3) cA0_129855339_50000000 (⟨by rw [nlo_47, vB40_2770769301995, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith, by rw [nhi_47, vB40_3109888511976, cA0_129855339_50000000_eq, vB40_2855549103185]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_44, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_44, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.leaf (47 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (48 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (0 : Fin 3) cA0_66855339_25000000 (⟨by rw [nlo_46, vB40_2855549103185, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_46, vB40_3109888511976, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
      (Cover.node (1 : Fin 3) cA1_66855339_25000000 (⟨by rw [nlo_45, vB40_2770769301995, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_45, vB40_3109888511976, cA1_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
       (Cover.leaf (49 : Fin 62) (by decide) (by decide) rfl)
       (Cover.leaf (50 : Fin 62) (by decide) (by decide) rfl))
      (Cover.leaf (51 : Fin 62) (by decide) (by decide) rfl)))))
  (Cover.node (2 : Fin 3) cA2_2347_1000 (⟨by rw [nlo_58, vB40_2390338278785, cA2_2347_1000_eq, vB40_2580553790390]; linarith, by rw [nhi_58, vB40_2708668885259, cA2_2347_1000_eq, vB40_2580553790390]; linarith⟩)
   (Cover.node (0 : Fin 3) cA0_63_25 (⟨by rw [nlo_56, vB40_2708646895026, cA0_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_56, vB40_3109888511976, cA0_63_25_eq, vB40_2770769301995]; linarith⟩)
    (Cover.node (0 : Fin 3) cA0_9967_4000 (⟨by rw [nlo_52, vB40_2708646895026, cA0_9967_4000_eq, vB40_2739708098510]; linarith, by rw [nhi_52, vB40_2770769301995, cA0_9967_4000_eq, vB40_2739708098510]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_50, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_50, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (52 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (53 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_51, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_51, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (54 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (55 : Fin 62) (by decide) (by decide) rfl)))
    (Cover.node (0 : Fin 3) cA0_66855339_25000000 (⟨by rw [nlo_55, vB40_2770769301995, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith, by rw [nhi_55, vB40_3109888511976, cA0_66855339_25000000_eq, vB40_2940328904376]; linarith⟩)
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_53, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_53, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (56 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (57 : Fin 62) (by decide) (by decide) rfl))
     (Cover.node (1 : Fin 3) cA1_63_25 (⟨by rw [nlo_54, vB40_2708646895026, cA1_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_54, vB40_3109888511976, cA1_63_25_eq, vB40_2770769301995]; linarith⟩)
      (Cover.leaf (58 : Fin 62) (by decide) (by decide) rfl)
      (Cover.leaf (59 : Fin 62) (by decide) (by decide) rfl))))
   (Cover.node (0 : Fin 3) cA0_63_25 (⟨by rw [nlo_57, vB40_2708646895026, cA0_63_25_eq, vB40_2770769301995]; linarith, by rw [nhi_57, vB40_3109888511976, cA0_63_25_eq, vB40_2770769301995]; linarith⟩)
    (Cover.leaf (60 : Fin 62) (by decide) (by decide) rfl)
    (Cover.leaf (61 : Fin 62) (by decide) (by decide) rfl))))

/-- R1: the hcore, replayed through the tree.  Statement is the
verbatim hypothesis shape of `bank_QZECFICwt2A_of_core`
(NliBanks19.lean:256). -/
theorem wt2a_hcore_cover : ∀ y4 y5 y6 : ℝ,
    (2:ℝ) * Kepler.Text.hminus ≤ y4 → y4 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ y5 → y5 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ y6 → y6 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF y4 y5 y6 := by
  intro y4 y5 y6 h4 h4' h5 h5' h6 h6' hd
  refine cover_sound hsoundWt2A coverWt2A
    (fun i => if (i : ℕ) = 0 then y4 else if (i : ℕ) = 1 then y5 else y6) ?_
    h4 h4' h5 h5' h6 h6' hd
  intro i
  fin_cases i
  · show (topLoWt2A (0 : Fin 3)).value ≤ y4 ∧ y4 ≤ (topHiWt2A (0 : Fin 3)).value
    exact ⟨by linarith [vTL0, Kepler.NliBanks17.nb17_two_hminus_bounds.1, h4],
      by linarith [vTH0, h4']⟩
  · show (topLoWt2A (1 : Fin 3)).value ≤ y5 ∧ y5 ≤ (topHiWt2A (1 : Fin 3)).value
    exact ⟨by linarith [vTL1, Kepler.NliBanks17.nb17_two_hminus_bounds.1, h5],
      by linarith [vTH1, h5']⟩
  · show (topLoWt2A (2 : Fin 3)).value ≤ y6 ∧ y6 ≤ (topHiWt2A (2 : Fin 3)).value
    exact ⟨by linarith [vTL2, h6],
      by linarith [vTH2, Kepler.NliBanks17.nb17_two_hminus_bounds.2, h6']⟩

theorem bankQZECFICwt2A_cover : Kepler.Text.bank_QZECFICwt2A :=
  Kepler.NliBanks19.bank_QZECFICwt2A_of_core wt2a_hcore_cover

/-- R5: boundary-overlap control (T-5).  r5Point takes the cut
value on axis 0 and the shared-box lo on the other axes, so it
lies in BOTH closed sibling boxes. -/
def r5Point : Fin 3 → DC := fun i => match (i : ℕ) with
  | 0 => (⟨40, 2770769301995, 2770769301995⟩ : DC)
  | 1 => (⟨40, 2708646895026, 2708646895026⟩ : DC)
  | _ => (⟨40, 2580553790390, 2580553790390⟩ : DC)

noncomputable def r5Real : Fin 3 → ℝ := fun i => (r5Point i).value

theorem r5_L0lo : ((rowsWt2A (60 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [show ((rowsWt2A (60 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) from by decide, vB40_2708646895026]; norm_num
theorem r5_L0hi : ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [show ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) from by decide, vB40_2770769301995]; norm_num
theorem r5_L1lo : ((rowsWt2A (60 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [show ((rowsWt2A (60 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) from by decide, vB40_2708646895026]; norm_num
theorem r5_L1hi : ((rowsWt2A (60 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [show ((rowsWt2A (60 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) from by decide, vB40_3109888511976]; norm_num
theorem r5_L2lo : ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [show ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) from by decide, vB40_2580553790390]; norm_num
theorem r5_L2hi : ((rowsWt2A (60 : Fin 62)).boxHi (2 : Fin 3)).value = 2.4635200000002441811375319957733154296875 := by rw [show ((rowsWt2A (60 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) from by decide, vB40_2708668885259]; norm_num
theorem r5_R0lo : ((rowsWt2A (61 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [show ((rowsWt2A (61 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) from by decide, vB40_2770769301995]; norm_num
theorem r5_R0hi : ((rowsWt2A (61 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [show ((rowsWt2A (61 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) from by decide, vB40_3109888511976]; norm_num
theorem r5_R1lo : ((rowsWt2A (61 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [show ((rowsWt2A (61 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) from by decide, vB40_2708646895026]; norm_num
theorem r5_R1hi : ((rowsWt2A (61 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [show ((rowsWt2A (61 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) from by decide, vB40_3109888511976]; norm_num
theorem r5_R2lo : ((rowsWt2A (61 : Fin 62)).boxLo (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [show ((rowsWt2A (61 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) from by decide, vB40_2580553790390]; norm_num
theorem r5_R2hi : ((rowsWt2A (61 : Fin 62)).boxHi (2 : Fin 3)).value = 2.4635200000002441811375319957733154296875 := by rw [show ((rowsWt2A (61 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) from by decide, vB40_2708668885259]; norm_num
theorem r5P0 : (r5Point (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [show (r5Point (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) from by decide, vB40_2770769301995]; norm_num
theorem r5P1 : (r5Point (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [show (r5Point (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) from by decide, vB40_2708646895026]; norm_num
theorem r5P2 : (r5Point (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [show (r5Point (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) from by decide, vB40_2580553790390]; norm_num

theorem r5_mem : (r5Real ∈ rowBox (rowsWt2A (60 : Fin 62))) ∧
    (r5Real ∈ rowBox (rowsWt2A (61 : Fin 62))) := by
  have h0 : r5Real (0 : Fin 3) = (r5Point (0 : Fin 3)).value := rfl
  have h1 : r5Real (1 : Fin 3) = (r5Point (1 : Fin 3)).value := rfl
  have h2 : r5Real (2 : Fin 3) = (r5Point (2 : Fin 3)).value := rfl
  refine ⟨?_, ?_⟩ <;> intro i
  · fin_cases i
    · show ((rowsWt2A (60 : Fin 62)).boxLo (0 : Fin 3)).value ≤ r5Real (0 : Fin 3) ∧ r5Real (0 : Fin 3) ≤ ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)).value
      rw [r5_L0lo, r5_L0hi, h0, r5P0]
      norm_num
    · show ((rowsWt2A (60 : Fin 62)).boxLo (1 : Fin 3)).value ≤ r5Real (1 : Fin 3) ∧ r5Real (1 : Fin 3) ≤ ((rowsWt2A (60 : Fin 62)).boxHi (1 : Fin 3)).value
      rw [r5_L1lo, r5_L1hi, h1, r5P1]
      norm_num
    · show ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)).value ≤ r5Real (2 : Fin 3) ∧ r5Real (2 : Fin 3) ≤ ((rowsWt2A (60 : Fin 62)).boxHi (2 : Fin 3)).value
      rw [r5_L2lo, r5_L2hi, h2, r5P2]
      norm_num
  · fin_cases i
    · show ((rowsWt2A (61 : Fin 62)).boxLo (0 : Fin 3)).value ≤ r5Real (0 : Fin 3) ∧ r5Real (0 : Fin 3) ≤ ((rowsWt2A (61 : Fin 62)).boxHi (0 : Fin 3)).value
      rw [r5_R0lo, r5_R0hi, h0, r5P0]
      norm_num
    · show ((rowsWt2A (61 : Fin 62)).boxLo (1 : Fin 3)).value ≤ r5Real (1 : Fin 3) ∧ r5Real (1 : Fin 3) ≤ ((rowsWt2A (61 : Fin 62)).boxHi (1 : Fin 3)).value
      rw [r5_R1lo, r5_R1hi, h1, r5P1]
      norm_num
    · show ((rowsWt2A (61 : Fin 62)).boxLo (2 : Fin 3)).value ≤ r5Real (2 : Fin 3) ∧ r5Real (2 : Fin 3) ≤ ((rowsWt2A (61 : Fin 62)).boxHi (2 : Fin 3)).value
      rw [r5_R2lo, r5_R2hi, h2, r5P2]
      norm_num


#print axioms wt2a_hcore_cover
#print axioms bankQZECFICwt2A_cover

end Kepler.NliKit.BoxTreeWt2A

import Kepler.NliBanks26

set_option maxHeartbeats 16000000

namespace Kepler.NliBanks27
open Kepler.Text
open Kepler.NliBanks19
open Kepler.NliBanks20
open Kepler.NliBanks22
open Kepler.NliBanks23
open Kepler.NliBanks24
open Kepler.NliBanks25
open Kepler.NliBanks26

theorem wt2a_layer0 {y4 y5 y6 : ℝ}
    (h4 : (2.4635:ℝ) ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : (2.4635:ℝ) ≤ y5) (h5' : y5 ≤ Real.sqrt 8)
    (h6 : (2:ℝ) ≤ y6) (h6' : y6 ≤ (2.058:ℝ))
    (hd : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  by_cases hs4_r : y4 ≤ (2.52:ℝ)
  ·
    by_cases hs4_L : y4 ≤ (2.49175:ℝ)
    ·
      by_cases hs4_LL : y4 ≤ (2.477625:ℝ)
      ·
        by_cases hs5_LLL : y5 ≤ (2.52:ℝ)
        ·
          by_cases hs5_LLLL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks22.cell10_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell15_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_LLLR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks22.cell05_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks24.cell25_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs5_LLR : y5 ≤ (2.52:ℝ)
        ·
          by_cases hs5_LLRL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks22.cell09_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell14_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_LLRR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks22.cell07_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks24.cell26_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs4_LR : y4 ≤ (2.505875:ℝ)
      ·
        by_cases hs5_LRL : y5 ≤ (2.52:ℝ)
        ·
          by_cases hs5_LRLL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks22.cell08_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell13_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_LRLR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks22.cell06_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks24.cell27_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs5_LRR : y5 ≤ (2.52:ℝ)
        ·
          by_cases hs5_LRRL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_LRRR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks22.cell04_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks24.cell28_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
  ·
    by_cases hs4_R : y4 ≤ (2.59710678:ℝ)
    ·
      by_cases hs5_RL : y5 ≤ (2.49175:ℝ)
      ·
        by_cases hs4_RLL : y4 ≤ (2.55855339:ℝ)
        ·
          by_cases hs5_RLLL : y5 ≤ (2.477625:ℝ)
          ·
            exact Kepler.NliBanks23.cell11_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell16_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_RLLR : y5 ≤ (2.477625:ℝ)
          ·
            exact Kepler.NliBanks23.cell19_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell21_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs5_RLR : y5 ≤ (2.52:ℝ)
        ·
          exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_RLRR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks22.cell01_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks24.cell24_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs4_RR : y4 ≤ (2.67421356:ℝ)
      ·
        by_cases hs5_RRL : y5 ≤ (2.52:ℝ)
        ·
          by_cases hs5_RRLL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs5_RRLR : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks23.cell18_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks24.cell29_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
      ·
        by_cases hs5_RRR : y5 ≤ (2.49175:ℝ)
        ·
          by_cases hs4_RRRL : y4 ≤ (2.75132034:ℝ)
          ·
            exact Kepler.NliBanks24.cell22_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
        ·
          by_cases hs5_RRRR : y5 ≤ (2.52:ℝ)
          ·
            by_cases hs4_RRRRL : y4 ≤ (2.75132034:ℝ)
            ·
              exact Kepler.NliBanks24.cell23_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
            ·
              exact ((Kepler.NliBanks24.cell31_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd

theorem wt2a_layer1 {y4 y5 y6 : ℝ}
    (h4 : (2.4635:ℝ) ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : (2.4635:ℝ) ≤ y5) (h5' : y5 ≤ Real.sqrt 8)
    (h6 : (2.058:ℝ) ≤ y6) (h6' : y6 ≤ (2.174:ℝ))
    (hd : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  by_cases hs4_r : y4 ≤ (2.52:ℝ)
  ·
    by_cases hs4_L : y4 ≤ (2.49175:ℝ)
    ·
      by_cases hs5_LL : y5 ≤ (2.67421356:ℝ)
      ·
        by_cases hs5_LLL : y5 ≤ (2.52:ℝ)
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs4_LLLR : y4 ≤ (2.477625:ℝ)
          ·
            exact Kepler.NliBanks25.cell38_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell39_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs4_LLR : y4 ≤ (2.477625:ℝ)
        ·
          exact Kepler.NliBanks25.cell45_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell46_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs5_LR : y5 ≤ (2.67421356:ℝ)
      ·
        by_cases hs5_LRL : y5 ≤ (2.52:ℝ)
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          by_cases hs4_LRLR : y4 ≤ (2.505875:ℝ)
          ·
            exact Kepler.NliBanks25.cell40_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell41_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs4_LRR : y4 ≤ (2.505875:ℝ)
        ·
          exact Kepler.NliBanks25.cell47_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          exact ((Kepler.NliBanks25.cell51_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
  ·
    by_cases hs5_R : y5 ≤ (2.52:ℝ)
    ·
      by_cases hs4_RL : y4 ≤ (2.59710678:ℝ)
      ·
        by_cases hs5_RLL : y5 ≤ (2.49175:ℝ)
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        by_cases hs4_RLR : y4 ≤ (2.67421356:ℝ)
        ·
          by_cases hs5_RLRL : y5 ≤ (2.49175:ℝ)
          ·
            exact Kepler.NliBanks25.cell42_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs4_RR : y4 ≤ (2.59710678:ℝ)
      ·
        by_cases hs5_RRL : y5 ≤ (2.67421356:ℝ)
        ·
          exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
        ·
          exact ((Kepler.NliBanks25.cell49_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
      ·
        by_cases hs4_RRR : y4 ≤ (2.67421356:ℝ)
        ·
          by_cases hs5_RRRL : y5 ≤ (2.67421356:ℝ)
          ·
            exact Kepler.NliBanks25.cell44_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell50_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
        ·
          exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim

theorem wt2a_layer2 {y4 y5 y6 : ℝ}
    (h4 : (2.4635:ℝ) ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : (2.4635:ℝ) ≤ y5) (h5' : y5 ≤ Real.sqrt 8)
    (h6 : (2.174:ℝ) ≤ y6) (h6' : y6 ≤ (2.347:ℝ))
    (hd : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  by_cases hs4_r : y4 ≤ (2.52:ℝ)
  ·
    by_cases hs4_L : y4 ≤ (2.49175:ℝ)
    ·
      by_cases hs5_LL : y5 ≤ (2.52:ℝ)
      ·
        exact Kepler.NliBanks26.cell54_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell55_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs5_LR : y5 ≤ (2.52:ℝ)
      ·
        exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
  ·
    by_cases hs4_R : y4 ≤ (2.67421356:ℝ)
    ·
      by_cases hs5_RL : y5 ≤ (2.52:ℝ)
      ·
        exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      by_cases hs5_RR : y5 ≤ (2.52:ℝ)
      ·
        exact ((Kepler.NliBanks26.cell58_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
      ·
        exact ((Kepler.NliBanks26.cell59_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim

theorem wt2a_layer3 {y4 y5 y6 : ℝ}
    (h4 : (2.4635:ℝ) ≤ y4) (h4' : y4 ≤ Real.sqrt 8)
    (h5 : (2.4635:ℝ) ≤ y5) (h5' : y5 ≤ Real.sqrt 8)
    (h6 : (2.347:ℝ) ≤ y6) (h6' : y6 ≤ (2.46352:ℝ))
    (hd : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  by_cases hs4_r : y4 ≤ (2.52:ℝ)
  ·
    exact Kepler.NliBanks26.cell61_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
  ·
    exact Kepler.NliBanks26.cell60_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd

theorem bank_wt2A : bank_QZECFICwt2A := by
  refine bank_QZECFICwt2A_of_core (fun y4 y5 y6 h4 h4' h5 h5' h6 h6' hd => ?_)
  have h4n : (2.4635:ℝ) ≤ y4 := by
    linarith [h4, Kepler.NliBanks17.nb17_two_hminus_bounds.1]
  have h5n : (2.4635:ℝ) ≤ y5 := by
    linarith [h5, Kepler.NliBanks17.nb17_two_hminus_bounds.1]
  have h6top : y6 ≤ (2.46352:ℝ) := by
    linarith [h6', Kepler.NliBanks17.nb17_two_hminus_bounds.2]
  by_cases hy60 : y6 ≤ (2.058:ℝ)
  · exact wt2a_layer0 h4n h4' h5n h5' h6 hy60 hd
  · by_cases hy61 : y6 ≤ (2.174:ℝ)
    · exact wt2a_layer1 h4n h4' h5n h5' (by linarith [hy60]) hy61 hd
    · by_cases hy62 : y6 ≤ (2.347:ℝ)
      · exact wt2a_layer2 h4n h4' h5n h5' (by linarith [hy61]) hy62 hd
      · exact wt2a_layer3 h4n h4' h5n h5' (by linarith [hy62]) h6top hd

end Kepler.NliBanks27

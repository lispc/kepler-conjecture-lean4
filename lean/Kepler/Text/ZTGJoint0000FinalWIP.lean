import Kepler.Text.ZTGJoint0000Concave

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

theorem nliRestZTGIJCF4_0_0_0_0_of_nonpos
    (h0l : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y1 ∈ Set.Ioo (2 * hminus) 2.52 →
      ztgDMainSecond_y1 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (h0r : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y1 ∈ Set.Ioo 2.52 (2 * hplus) →
      ztgDMainSecond_y1 y1 y2 y3 y4 y5 y6 0 ≤ 0)
    (h1 : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y2 ∈ Set.Ioo 2 (2 * hminus) →
      ztgDMainSecond_y2 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (h2 : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y3 ∈ Set.Ioo 2 (2 * hminus) →
      ztgDMainSecond_y3 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (h3 : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y4 ∈ Set.Ioo 2 (2 * hminus) →
      ztgDMainSecond_y4 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (h4 : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y5 ∈ Set.Ioo 2 (2 * hminus) →
      ztgDMainSecond_y5 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (h5 : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y6 ∈ Set.Ioo 2 (2 * hminus) →
      ztgDMainSecond_y6 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    bank_ZTGIJCF4_0_0_0_0 :=
  nliRestZTGIJCF4_0_0_0_0_of_concave
    (ztg_concave_y1_left_of_nonpos h0l) (ztg_concave_y1_right_of_nonpos h0r)
    (ztg_concave_y2_whole_of_nonpos h1) (ztg_concave_y3_whole_of_nonpos h2)
    (ztg_concave_y4_whole_of_nonpos h3) (ztg_concave_y5_whole_of_nonpos h4)
    (ztg_concave_y6_whole_of_nonpos h5)

#print axioms nliRestZTGIJCF4_0_0_0_0_of_nonpos

end Kepler.Text

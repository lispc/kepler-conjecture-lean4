import Kepler.Text.FhbG3posCurve
import Kepler.Text.Gamma4ValCornerKit
import Kepler.Text.Gamma4WideKink

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- slot0 ('4', '4', '4', '4', 'x1', 'x2'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot0 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (-0.529911942912:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.529911942870:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey0 : (deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn0 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    nlinarith [hkey0, sq_nonneg (deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))]
  have hsq0 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) :=
    Real.sq_sqrt hnn0
  have hbr0 : |deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := by
    have hsp0 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey0, hsq0, hsp0]
    · nlinarith [hkey0, hsq0, hsp0]
  have hd0 : dihY 2 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) :=
    g3c_dihY_eq hbr0
  have hv0 : (-28.33972682229636745:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (-28.33972682229636729:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu0 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu0 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu0.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu0.1])).mpr (by nlinarith [hu0.2])
  have hpos0 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu0.1
  have hg0 : (-0.585798731697:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.585798731696:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos0]; nlinarith [hv0.1, hv0.2, hsu0.1, hsu0.2]
    · rw [div_le_iff₀ hpos0]; nlinarith [hv0.1, hv0.2, hsu0.1, hsu0.2]
  have hgp0L : (0.529911942871:ℝ) ≤ Real.arctan (0.585798731697) ∧
      Real.arctan (0.585798731697) ≤ (0.529911942912:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.585798731697)) (lo := (0.529911942871))
      (hi := (0.529911942912)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp0H : (0.529911942870:ℝ) ≤ Real.arctan (0.585798731696) ∧
      Real.arctan (0.585798731696) ≤ (0.529911942911:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.585798731696)) (lo := (0.529911942870))
      (hi := (0.529911942911)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal0 : (-0.529911942912:ℝ) ≤ Real.arctan (-0.585798731697) := by
    rw [Real.arctan_neg]; linarith [hgp0L.2]
  have hgah0 : Real.arctan (-0.585798731696) ≤ (-0.529911942870:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp0H.1]
  have ha0 : (-0.529911942912:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.529911942870:ℝ) :=
    g3c_arctan_of_bounds hg0.1 hg0.2 hgal0 hgah0
  exact ⟨hd0, ha0.1, ha0.2⟩

/-- slot1 ('4', '4', '4', 'x1', '4', 'x2'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot1 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 2 (2*hplus) 2 (fhbY2Star (2*hplus)) = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (0.148902042214:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey1 : (deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn1 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    nlinarith [hkey1, sq_nonneg (deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))]
  have hsq1 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) :=
    Real.sq_sqrt hnn1
  have hbr1 : |deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := by
    have hsp1 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey1, hsq1, hsp1]
    · nlinarith [hkey1, hsq1, hsp1]
  have hd1 : dihY 2 2 2 (2*hplus) 2 (fhbY2Star (2*hplus)) = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) :=
    g3c_dihY_eq hbr1
  have hv1 : (7.25728695400746380:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (7.25728695400746392:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu1 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu1 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu1.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu1.1])).mpr (by nlinarith [hu1.2])
  have hpos1 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu1.1
  have hg1 : (0.150012366734:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (0.150012366735:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos1]; nlinarith [hv1.1, hv1.2, hsu1.1, hsu1.2]
    · rw [div_le_iff₀ hpos1]; nlinarith [hv1.1, hv1.2, hsu1.1, hsu1.2]
  have hgp1L : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) ∧
      Real.arctan (0.150012366734) ≤ (0.148902042213:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366734)) (lo := (0.148902042172))
      (hi := (0.148902042213)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp1H : (0.148902042173:ℝ) ≤ Real.arctan (0.150012366735) ∧
      Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366735)) (lo := (0.148902042173))
      (hi := (0.148902042214)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal1 : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) := hgp1L.1
  have hgah1 : Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := hgp1H.2
  have ha1 : (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (0.148902042214:ℝ) :=
    g3c_arctan_of_bounds hg1.1 hg1.2 hgal1 hgah1
  exact ⟨hd1, ha1.1, ha1.2⟩

/-- slot2 ('4', '4', '4', 'x1', 'x2', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot2 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧
      (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (0.148902042214:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey2 : (deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn2 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) := by
    nlinarith [hkey2, sq_nonneg (deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))]
  have hsq2 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) :=
    Real.sq_sqrt hnn2
  have hbr2 : |deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) := by
    have hsp2 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey2, hsq2, hsp2]
    · nlinarith [hkey2, hsq2, hsp2]
  have hd2 : dihY 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) :=
    g3c_dihY_eq hbr2
  have hv2 : (7.25728695400746380:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ∧ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ≤ (7.25728695400746392:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu2 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu2 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu2.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu2.1])).mpr (by nlinarith [hu2.2])
  have hpos2 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu2.1
  have hg2 : (0.150012366734:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (0.150012366735:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos2]; nlinarith [hv2.1, hv2.2, hsu2.1, hsu2.2]
    · rw [div_le_iff₀ hpos2]; nlinarith [hv2.1, hv2.2, hsu2.1, hsu2.2]
  have hgp2L : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) ∧
      Real.arctan (0.150012366734) ≤ (0.148902042213:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366734)) (lo := (0.148902042172))
      (hi := (0.148902042213)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp2H : (0.148902042173:ℝ) ≤ Real.arctan (0.150012366735) ∧
      Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366735)) (lo := (0.148902042173))
      (hi := (0.148902042214)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal2 : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) := hgp2L.1
  have hgah2 : Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := hgp2H.2
  have ha2 : (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (0.148902042214:ℝ) :=
    g3c_arctan_of_bounds hg2.1 hg2.2 hgal2 hgah2
  exact ⟨hd2, ha2.1, ha2.2⟩

/-- slot3 ('4', '4', '4', 'x2', '4', 'x1'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot3 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 2 (fhbY2Star (2*hplus)) 2 (2*hplus) = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ∧
      (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.496246573777:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey3 : (deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn3 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) := by
    nlinarith [hkey3, sq_nonneg (deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))]
  have hsq3 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) :=
    Real.sq_sqrt hnn3
  have hbr3 : |deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) := by
    have hsp3 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey3, hsq3, hsp3]
    · nlinarith [hkey3, hsq3, hsp3]
  have hd3 : dihY 2 2 2 (fhbY2Star (2*hplus)) 2 (2*hplus) = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) :=
    g3c_dihY_eq hbr3
  have hv3 : (-26.19368622801492776:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) ∧ -(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) ≤ (-26.19368622801492768:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu3 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu3 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu3.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu3.1])).mpr (by nlinarith [hu3.2])
  have hpos3 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu3.1
  have hg3 : (-0.541438817215:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.541438817214:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos3]; nlinarith [hv3.1, hv3.2, hsu3.1, hsu3.2]
    · rw [div_le_iff₀ hpos3]; nlinarith [hv3.1, hv3.2, hsu3.1, hsu3.2]
  have hgp3L : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817215) ∧
      Real.arctan (0.541438817215) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817215)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp3H : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817214) ∧
      Real.arctan (0.541438817214) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817214)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal3 : (-0.496246573818:ℝ) ≤ Real.arctan (-0.541438817215) := by
    rw [Real.arctan_neg]; linarith [hgp3L.2]
  have hgah3 : Real.arctan (-0.541438817214) ≤ (-0.496246573777:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp3H.1]
  have ha3 : (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.496246573777:ℝ) :=
    g3c_arctan_of_bounds hg3.1 hg3.2 hgal3 hgah3
  exact ⟨hd3, ha3.1, ha3.2⟩

/-- slot4 ('4', '4', 'x1', 'x2', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot4 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧
      (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.496246573777:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey4 : (deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn4 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) := by
    nlinarith [hkey4, sq_nonneg (deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))]
  have hsq4 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn4
  have hbr4 : |deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) := by
    have hsp4 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey4, hsq4, hsp4]
    · nlinarith [hkey4, hsq4, hsp4]
  have hd4 : dihY 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr4
  have hv4 : (-26.19368622801492776:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ∧ -(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ≤ (-26.19368622801492768:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu4 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu4 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu4.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu4.1])).mpr (by nlinarith [hu4.2])
  have hpos4 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu4.1
  have hg4 : (-0.541438817215:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.541438817214:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos4]; nlinarith [hv4.1, hv4.2, hsu4.1, hsu4.2]
    · rw [div_le_iff₀ hpos4]; nlinarith [hv4.1, hv4.2, hsu4.1, hsu4.2]
  have hgp4L : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817215) ∧
      Real.arctan (0.541438817215) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817215)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp4H : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817214) ∧
      Real.arctan (0.541438817214) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817214)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal4 : (-0.496246573818:ℝ) ≤ Real.arctan (-0.541438817215) := by
    rw [Real.arctan_neg]; linarith [hgp4L.2]
  have hgah4 : Real.arctan (-0.541438817214) ≤ (-0.496246573777:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp4H.1]
  have ha4 : (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.496246573777:ℝ) :=
    g3c_arctan_of_bounds hg4.1 hg4.2 hgal4 hgah4
  exact ⟨hd4, ha4.1, ha4.2⟩

/-- slot5 ('4', '4', 'x2', '4', 'x1', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot5 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ∧
      (-0.540979333255:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ≤ (-0.540979333213:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey5 : (deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn5 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) := by
    nlinarith [hkey5, sq_nonneg (deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))]
  have hsq5 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) :=
    Real.sq_sqrt hnn5
  have hbr5 : |deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) := by
    have hsp5 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey5, hsq5, hsp5]
    · nlinarith [hkey5, hsq5, hsp5]
  have hd5 : dihY 2 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) :=
    g3c_dihY_eq hbr5
  have hv5 : (-29.06360072599253620:ℝ) ≤ -(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) ∧ -(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) ≤ (-29.06360072599253608:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu5 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu5 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu5.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu5.1])).mpr (by nlinarith [hu5.2])
  have hpos5 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu5.1
  have hg5 : (-0.600761628741:ℝ) ≤ (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ≤ (-0.600761628740:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos5]; nlinarith [hv5.1, hv5.2, hsu5.1, hsu5.2]
    · rw [div_le_iff₀ hpos5]; nlinarith [hv5.1, hv5.2, hsu5.1, hsu5.2]
  have hgp5L : (0.540979333214:ℝ) ≤ Real.arctan (0.600761628741) ∧
      Real.arctan (0.600761628741) ≤ (0.540979333255:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.600761628741)) (lo := (0.540979333214))
      (hi := (0.540979333255)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp5H : (0.540979333213:ℝ) ≤ Real.arctan (0.600761628740) ∧
      Real.arctan (0.600761628740) ≤ (0.540979333254:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.600761628740)) (lo := (0.540979333213))
      (hi := (0.540979333254)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal5 : (-0.540979333255:ℝ) ≤ Real.arctan (-0.600761628741) := by
    rw [Real.arctan_neg]; linarith [hgp5L.2]
  have hgah5 : Real.arctan (-0.600761628740) ≤ (-0.540979333213:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp5H.1]
  have ha5 : (-0.540979333255:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2))) ≤ (-0.540979333213:ℝ) :=
    g3c_arctan_of_bounds hg5.1 hg5.2 hgal5 hgah5
  exact ⟨hd5, ha5.1, ha5.2⟩

/-- slot6 ('4', 'x1', '4', '4', '4', 'x2'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot6 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (-0.540979333255:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.540979333213:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey6 : (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn6 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) := by
    nlinarith [hkey6, sq_nonneg (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))]
  have hsq6 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) :=
    Real.sq_sqrt hnn6
  have hbr6 : |deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := by
    have hsp6 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey6, hsq6, hsp6]
    · nlinarith [hkey6, hsq6, hsp6]
  have hd6 : dihY 2 (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) :=
    g3c_dihY_eq hbr6
  have hv6 : (-29.06360072599253620:ℝ) ≤ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (-29.06360072599253608:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu6 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ∧
      4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu6 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu6.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu6.1])).mpr (by nlinarith [hu6.2])
  have hpos6 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu6.1
  have hg6 : (-0.600761628741:ℝ) ≤ (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧
      (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.600761628740:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos6]; nlinarith [hv6.1, hv6.2, hsu6.1, hsu6.2]
    · rw [div_le_iff₀ hpos6]; nlinarith [hv6.1, hv6.2, hsu6.1, hsu6.2]
  have hgp6L : (0.540979333214:ℝ) ≤ Real.arctan (0.600761628741) ∧
      Real.arctan (0.600761628741) ≤ (0.540979333255:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.600761628741)) (lo := (0.540979333214))
      (hi := (0.540979333255)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp6H : (0.540979333213:ℝ) ≤ Real.arctan (0.600761628740) ∧
      Real.arctan (0.600761628740) ≤ (0.540979333254:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.600761628740)) (lo := (0.540979333213))
      (hi := (0.540979333254)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal6 : (-0.540979333255:ℝ) ≤ Real.arctan (-0.600761628741) := by
    rw [Real.arctan_neg]; linarith [hgp6L.2]
  have hgah6 : Real.arctan (-0.600761628740) ≤ (-0.540979333213:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp6H.1]
  have ha6 : (-0.540979333255:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)))) ≤ (-0.540979333213:ℝ) :=
    g3c_arctan_of_bounds hg6.1 hg6.2 hgal6 hgah6
  exact ⟨hd6, ha6.1, ha6.2⟩

/-- slot7 ('4', 'x1', '4', 'x2', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot7 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 (2*hplus) 2 (fhbY2Star (2*hplus)) 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧
      (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.496246573777:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey7 : (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn7 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) := by
    nlinarith [hkey7, sq_nonneg (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))]
  have hsq7 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn7
  have hbr7 : |deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) := by
    have hsp7 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey7, hsq7, hsp7]
    · nlinarith [hkey7, hsq7, hsp7]
  have hd7 : dihY 2 (2*hplus) 2 (fhbY2Star (2*hplus)) 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr7
  have hv7 : (-26.19368622801492776:ℝ) ≤ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ∧ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ≤ (-26.19368622801492768:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu7 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu7 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu7.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu7.1])).mpr (by nlinarith [hu7.2])
  have hpos7 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu7.1
  have hg7 : (-0.541438817215:ℝ) ≤ (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.541438817214:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos7]; nlinarith [hv7.1, hv7.2, hsu7.1, hsu7.2]
    · rw [div_le_iff₀ hpos7]; nlinarith [hv7.1, hv7.2, hsu7.1, hsu7.2]
  have hgp7L : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817215) ∧
      Real.arctan (0.541438817215) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817215)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp7H : (0.496246573777:ℝ) ≤ Real.arctan (0.541438817214) ∧
      Real.arctan (0.541438817214) ≤ (0.496246573818:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.541438817214)) (lo := (0.496246573777))
      (hi := (0.496246573818)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal7 : (-0.496246573818:ℝ) ≤ Real.arctan (-0.541438817215) := by
    rw [Real.arctan_neg]; linarith [hgp7L.2]
  have hgah7 : Real.arctan (-0.541438817214) ≤ (-0.496246573777:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp7H.1]
  have ha7 : (-0.496246573818:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2))) ≤ (-0.496246573777:ℝ) :=
    g3c_arctan_of_bounds hg7.1 hg7.2 hgal7 hgah7
  exact ⟨hd7, ha7.1, ha7.2⟩

/-- slot8 ('4', 'x1', 'x2', '4', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot8 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-0.529911942912:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.529911942870:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey8 : (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn8 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) := by
    nlinarith [hkey8, sq_nonneg (deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))]
  have hsq8 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn8
  have hbr8 : |deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) := by
    have hsp8 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey8, hsq8, hsp8]
    · nlinarith [hkey8, hsq8, hsp8]
  have hd8 : dihY 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr8
  have hv8 : (-28.33972682229636745:ℝ) ≤ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ∧ -(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ≤ (-28.33972682229636729:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu8 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu8 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu8.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu8.1])).mpr (by nlinarith [hu8.2])
  have hpos8 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu8.1
  have hg8 : (-0.585798731697:ℝ) ≤ (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.585798731696:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos8]; nlinarith [hv8.1, hv8.2, hsu8.1, hsu8.2]
    · rw [div_le_iff₀ hpos8]; nlinarith [hv8.1, hv8.2, hsu8.1, hsu8.2]
  have hgp8L : (0.529911942871:ℝ) ≤ Real.arctan (0.585798731697) ∧
      Real.arctan (0.585798731697) ≤ (0.529911942912:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.585798731697)) (lo := (0.529911942871))
      (hi := (0.529911942912)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp8H : (0.529911942870:ℝ) ≤ Real.arctan (0.585798731696) ∧
      Real.arctan (0.585798731696) ≤ (0.529911942911:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.585798731696)) (lo := (0.529911942870))
      (hi := (0.529911942911)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal8 : (-0.529911942912:ℝ) ≤ Real.arctan (-0.585798731697) := by
    rw [Real.arctan_neg]; linarith [hgp8L.2]
  have hgah8 : Real.arctan (-0.585798731696) ≤ (-0.529911942870:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp8H.1]
  have ha8 : (-0.529911942912:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.529911942870:ℝ) :=
    g3c_arctan_of_bounds hg8.1 hg8.2 hgal8 hgah8
  exact ⟨hd8, ha8.1, ha8.2⟩

/-- slot9 ('4', 'x2', '4', 'x1', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot9 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ∧
      (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ≤ (0.148902042214:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey9 : (deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) ^ 2 < 4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn9 : (0:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) := by
    nlinarith [hkey9, sq_nonneg (deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))]
  have hsq9 : (Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ^ 2 = 4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn9
  have hbr9 : |deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)| < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) := by
    have hsp9 : (0:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey9, hsq9, hsp9]
    · nlinarith [hkey9, hsq9, hsp9]
  have hd9 : dihY 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr9
  have hv9 : (7.25728695400746380:ℝ) ≤ -(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) ∧ -(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) ≤ (7.25728695400746392:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu9 : (2340.42358026057583532:ℝ) ≤ 4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) ∧
      4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) ≤ (2340.42358026057585906:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu9 : (48.37792451377565903:ℝ) ≤ Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) ≤ (48.37792451377565928:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu9.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu9.1])).mpr (by nlinarith [hu9.2])
  have hpos9 : (0:ℝ) < Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (48.37792451377565903) by norm_num) hsu9.1
  have hg9 : (0.150012366734:ℝ) ≤ (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ≤ (0.150012366735:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos9]; nlinarith [hv9.1, hv9.2, hsu9.1, hsu9.2]
    · rw [div_le_iff₀ hpos9]; nlinarith [hv9.1, hv9.2, hsu9.1, hsu9.2]
  have hgp9L : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) ∧
      Real.arctan (0.150012366734) ≤ (0.148902042213:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366734)) (lo := (0.148902042172))
      (hi := (0.148902042213)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp9H : (0.148902042173:ℝ) ≤ Real.arctan (0.150012366735) ∧
      Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.150012366735)) (lo := (0.148902042173))
      (hi := (0.148902042214)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal9 : (0.148902042172:ℝ) ≤ Real.arctan (0.150012366734) := hgp9L.1
  have hgah9 : Real.arctan (0.150012366735) ≤ (0.148902042214:ℝ) := hgp9H.2
  have ha9 : (0.148902042172:ℝ) ≤ Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2)) / Real.sqrt (4 * (2 * 2) * deltaX (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2))) ≤ (0.148902042214:ℝ) :=
    g3c_arctan_of_bounds hg9.1 hg9.2 hgal9 hgah9
  exact ⟨hd9, ha9.1, ha9.2⟩

/-- slot10 ('x1', '4', '4', '4', 'x2', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot10 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) 2 = Real.pi / 2 + Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧
      (-0.132091901889:ℝ) ≤ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (-0.132091901847:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey10 : (deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ^ 2 < 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn10 : (0:ℝ) ≤ 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) := by
    nlinarith [hkey10, sq_nonneg (deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))]
  have hsq10 : (Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ^ 2 = 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) :=
    Real.sq_sqrt hnn10
  have hbr10 : |deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)| < Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) := by
    have hsp10 : (0:ℝ) ≤ Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey10, hsq10, hsp10]
    · nlinarith [hkey10, hsq10, hsp10]
  have hd10 : dihY (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) :=
    g3c_dihY_eq hbr10
  have hv10 : (-8.51935316786109539:ℝ) ≤ -(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ∧ -(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ≤ (-8.51935316786109523:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu10 : (4111.38737155782250296:ℝ) ≤ 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ∧
      4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ≤ (4111.38737155782254466:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu10 : (64.12010115055825848:ℝ) ≤ Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ∧
      Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) ≤ (64.12010115055825881:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu10.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu10.1])).mpr (by nlinarith [hu10.2])
  have hpos10 : (0:ℝ) < Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (64.12010115055825848) by norm_num) hsu10.1
  have hg10 : (-0.132865560332:ℝ) ≤ (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧
      (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (-0.132865560331:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos10]; nlinarith [hv10.1, hv10.2, hsu10.1, hsu10.2]
    · rw [div_le_iff₀ hpos10]; nlinarith [hv10.1, hv10.2, hsu10.1, hsu10.2]
  have hgp10L : (0.132091901848:ℝ) ≤ Real.arctan (0.132865560332) ∧
      Real.arctan (0.132865560332) ≤ (0.132091901889:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.132865560332)) (lo := (0.132091901848))
      (hi := (0.132091901889)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp10H : (0.132091901847:ℝ) ≤ Real.arctan (0.132865560331) ∧
      Real.arctan (0.132865560331) ≤ (0.132091901888:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.132865560331)) (lo := (0.132091901847))
      (hi := (0.132091901888)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal10 : (-0.132091901889:ℝ) ≤ Real.arctan (-0.132865560332) := by
    rw [Real.arctan_neg]; linarith [hgp10L.2]
  have hgah10 : Real.arctan (-0.132865560331) ≤ (-0.132091901847:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp10H.1]
  have ha10 : (-0.132091901889:ℝ) ≤ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ∧ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2))) ≤ (-0.132091901847:ℝ) :=
    g3c_arctan_of_bounds hg10.1 hg10.2 hgal10 hgah10
  exact ⟨hd10, ha10.1, ha10.2⟩

/-- slot11 ('x1', 'x2', '4', '4', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot11 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-0.132091901889:ℝ) ≤ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.132091901847:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey11 : (deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ^ 2 < 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn11 : (0:ℝ) ≤ 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by
    nlinarith [hkey11, sq_nonneg (deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))]
  have hsq11 : (Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ^ 2 = 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn11
  have hbr11 : |deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)| < Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) := by
    have hsp11 : (0:ℝ) ≤ Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey11, hsq11, hsp11]
    · nlinarith [hkey11, hsq11, hsp11]
  have hd11 : dihY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr11
  have hv11 : (-8.51935316786109539:ℝ) ≤ -(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ∧ -(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ≤ (-8.51935316786109523:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu11 : (4111.38737155782250296:ℝ) ≤ 4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ∧
      4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ≤ (4111.38737155782254466:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu11 : (64.12010115055825848:ℝ) ≤ Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ≤ (64.12010115055825881:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu11.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu11.1])).mpr (by nlinarith [hu11.2])
  have hpos11 : (0:ℝ) < Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (64.12010115055825848) by norm_num) hsu11.1
  have hg11 : (-0.132865560332:ℝ) ≤ (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.132865560331:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos11]; nlinarith [hv11.1, hv11.2, hsu11.1, hsu11.2]
    · rw [div_le_iff₀ hpos11]; nlinarith [hv11.1, hv11.2, hsu11.1, hsu11.2]
  have hgp11L : (0.132091901848:ℝ) ≤ Real.arctan (0.132865560332) ∧
      Real.arctan (0.132865560332) ≤ (0.132091901889:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.132865560332)) (lo := (0.132091901848))
      (hi := (0.132091901889)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp11H : (0.132091901847:ℝ) ≤ Real.arctan (0.132865560331) ∧
      Real.arctan (0.132865560331) ≤ (0.132091901888:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.132865560331)) (lo := (0.132091901847))
      (hi := (0.132091901888)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal11 : (-0.132091901889:ℝ) ≤ Real.arctan (-0.132865560332) := by
    rw [Real.arctan_neg]; linarith [hgp11L.2]
  have hgah11 : Real.arctan (-0.132865560331) ≤ (-0.132091901847:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp11H.1]
  have ha11 : (-0.132091901889:ℝ) ≤ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * ((2*hplus) * (2*hplus)) * deltaX ((2*hplus) * (2*hplus)) (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.132091901847:ℝ) :=
    g3c_arctan_of_bounds hg11.1 hg11.2 hgal11 hgah11
  exact ⟨hd11, ha11.1, ha11.2⟩

/-- slot12 ('x2', '4', '4', '4', '4', 'x1'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot12 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY (fhbY2Star (2*hplus)) 2 2 2 2 (2*hplus) = Real.pi / 2 + Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ∧
      (-0.523896249177:ℝ) ≤ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ∧ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.523896249135:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey12 : (deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) ^ 2 < 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn12 : (0:ℝ) ≤ 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) := by
    nlinarith [hkey12, sq_nonneg (deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))]
  have hsq12 : (Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ^ 2 = 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) :=
    Real.sq_sqrt hnn12
  have hbr12 : |deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))| < Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) := by
    have hsp12 : (0:ℝ) ≤ Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey12, hsq12, hsp12]
    · nlinarith [hkey12, hsq12, hsp12]
  have hd12 : dihY (fhbY2Star (2*hplus)) 2 2 2 2 (2*hplus) = Real.pi / 2 +
      Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) :=
    g3c_dihY_eq hbr12
  have hv12 : (-28.77363917740657117:ℝ) ≤ -(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) ∧ -(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) ≤ (-28.77363917740657097:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu12 : (2480.35723785221098710:ℝ) ≤ 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) ∧
      4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)) ≤ (2480.35723785221101811:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu12 : (49.80318501714735700:ℝ) ≤ Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) ∧
      Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) ≤ (49.80318501714735733:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu12.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu12.1])).mpr (by nlinarith [hu12.2])
  have hpos12 : (0:ℝ) < Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) :=
    lt_of_lt_of_le (show (0:ℝ) < (49.80318501714735700) by norm_num) hsu12.1
  have hg12 : (-0.577746968744:ℝ) ≤ (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ∧
      (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.577746968743:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos12]; nlinarith [hv12.1, hv12.2, hsu12.1, hsu12.2]
    · rw [div_le_iff₀ hpos12]; nlinarith [hv12.1, hv12.2, hsu12.1, hsu12.2]
  have hgp12L : (0.523896249136:ℝ) ≤ Real.arctan (0.577746968744) ∧
      Real.arctan (0.577746968744) ≤ (0.523896249177:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.577746968744)) (lo := (0.523896249136))
      (hi := (0.523896249177)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp12H : (0.523896249135:ℝ) ≤ Real.arctan (0.577746968743) ∧
      Real.arctan (0.577746968743) ≤ (0.523896249176:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.577746968743)) (lo := (0.523896249135))
      (hi := (0.523896249176)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal12 : (-0.523896249177:ℝ) ≤ Real.arctan (-0.577746968744) := by
    rw [Real.arctan_neg]; linarith [hgp12L.2]
  have hgah12 : Real.arctan (-0.577746968743) ≤ (-0.523896249135:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp12H.1]
  have ha12 : (-0.523896249177:ℝ) ≤ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ∧ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus))) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2*hplus) * (2*hplus)))) ≤ (-0.523896249135:ℝ) :=
    g3c_arctan_of_bounds hg12.1 hg12.2 hgal12 hgah12
  exact ⟨hd12, ha12.1, ha12.2⟩

/-- slot13 ('x2', '4', 'x1', '4', '4', '4'): `dihY` reduction on the arctan branch plus the two-sided
Taylor bound for the slot arctan argument. -/
private lemma g3c_slot13 (hx2b1 : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus))
    (hx2b2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ (4.23915954149813404:ℝ))
    (hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus))) :
    dihY (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 2 = Real.pi / 2 + Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-0.523896249177:ℝ) ≤ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.523896249135:ℝ) := by
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hkey13 : (deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ^ 2 < 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) := by
    rw [hx2e]; unfold deltaX4 deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hnn13 : (0:ℝ) ≤ 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) := by
    nlinarith [hkey13, sq_nonneg (deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))]
  have hsq13 : (Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ^ 2 = 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) :=
    Real.sq_sqrt hnn13
  have hbr13 : |deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)| < Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) := by
    have hsp13 : (0:ℝ) ≤ Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) := Real.sqrt_nonneg _
    rw [abs_lt]; constructor
    · nlinarith [hkey13, hsq13, hsp13]
    · nlinarith [hkey13, hsq13, hsp13]
  have hd13 : dihY (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 2 = Real.pi / 2 +
      Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) :=
    g3c_dihY_eq hbr13
  have hv13 : (-28.77363917740657117:ℝ) ≤ -(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ∧ -(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ≤ (-28.77363917740657097:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX4; nlinarith [hx2b1, hx2b2, hx2prod]
  have hu13 : (2480.35723785221098710:ℝ) ≤ 4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) ∧
      4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2) ≤ (2480.35723785221101811:ℝ) := by
    constructor
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
    · rw [hx2e]; unfold deltaX; nlinarith [hx2b1, hx2b2, hx2prod]
  have hsu13 : (49.80318501714735700:ℝ) ≤ Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ∧
      Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) ≤ (49.80318501714735733:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hu13.1])
    · exact (Real.sqrt_le_left (by nlinarith [hu13.1])).mpr (by nlinarith [hu13.2])
  have hpos13 : (0:ℝ) < Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) :=
    lt_of_lt_of_le (show (0:ℝ) < (49.80318501714735700) by norm_num) hsu13.1
  have hg13 : (-0.577746968744:ℝ) ≤ (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧
      (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.577746968743:ℝ) := by
    constructor
    · rw [le_div_iff₀ hpos13]; nlinarith [hv13.1, hv13.2, hsu13.1, hsu13.2]
    · rw [div_le_iff₀ hpos13]; nlinarith [hv13.1, hv13.2, hsu13.1, hsu13.2]
  have hgp13L : (0.523896249136:ℝ) ≤ Real.arctan (0.577746968744) ∧
      Real.arctan (0.577746968744) ≤ (0.523896249177:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.577746968744)) (lo := (0.523896249136))
      (hi := (0.523896249177)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgp13H : (0.523896249135:ℝ) ≤ Real.arctan (0.577746968743) ∧
      Real.arctan (0.577746968743) ≤ (0.523896249176:ℝ) := by
    exact g4v_atan_pos_bounds (x := (0.577746968743)) (lo := (0.523896249135))
      (hi := (0.523896249176)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgal13 : (-0.523896249177:ℝ) ≤ Real.arctan (-0.577746968744) := by
    rw [Real.arctan_neg]; linarith [hgp13L.2]
  have hgah13 : Real.arctan (-0.577746968743) ≤ (-0.523896249135:ℝ) := by
    rw [Real.arctan_neg]; linarith [hgp13H.1]
  have ha13 : (-0.523896249177:ℝ) ≤ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ∧ Real.arctan (-(deltaX4 (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2)) / Real.sqrt (4 * (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) * deltaX (fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) (2 * 2) ((2*hplus) * (2*hplus)) (2 * 2) (2 * 2) (2 * 2))) ≤ (-0.523896249135:ℝ) :=
    g3c_arctan_of_bounds hg13.1 hg13.2 hgal13 hgah13
  exact ⟨hd13, ha13.1, ha13.2⟩

/-- **The endpoint certificate.**  On the seam curve at the double-radical
corner `(2*hplus)` (so `x1 = 43917129/6250000` and `fhbY2Star (2*hplus)` is the explicit
root), `gamma4fgcy ≥ 7e-3` (true value `+7.36233e-3`).  Proved from the
`g4v_corner_value_bounds` kit with the slot reductions `g3c_dihY_eq`; the
per-slot facts are `g3c_slot{i}` above. -/
theorem g3c_endpoint_gamma4 :
    (0.007 : ℝ) ≤ gamma4fgcy (2 * hplus) (fhbY2Star (2 * hplus)) 2 2 2 2 lmfun := by
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have h1lo : 2 * hminus ≤ (2 * hplus) := by
    have e1 : (2:ℝ) * hminus ≤ 2.46352 := hm.2
    have e2 : (2:ℝ) * hplus = 2.6508 := by norm_num [hplus]
    linarith
  have hsD : fhbD4 ((43917129/6250000 : ℝ)) = 84981419701437051/6103515625000000 := by
    norm_num [fhbD4]
  have hs : (3.73140131906009895:ℝ) ≤ Real.sqrt (fhbD4 (43917129/6250000)) ∧
            Real.sqrt (fhbD4 (43917129/6250000)) ≤ 3.73140131906009896 := by
    rw [hsD]; constructor
    · exact Real.le_sqrt_of_sq_le (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hx2e : (2*hplus) * (2*hplus) = 43917129/6250000 := by norm_num [hplus]
  have hx2 : fhbY2Star (2*hplus) * fhbY2Star (2*hplus)
      = 4 - (511 / 4489) * ((2*hplus)*(2*hplus))
        + (1250 / 4489) * Real.sqrt (fhbD4 ((2*hplus)*(2*hplus))) :=
    g3c_curve_x2 h1lo (le_refl (2 * hplus))
  have hx2b : (4.23915954149813403:ℝ) ≤ fhbY2Star (2*hplus) * fhbY2Star (2*hplus)
      ∧ fhbY2Star (2*hplus) * fhbY2Star (2*hplus) ≤ 4.23915954149813404 := by
    rw [hx2, hx2e]; constructor
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hx2prod : (0:ℝ) ≤ (fhbY2Star (2*hplus) * fhbY2Star (2*hplus) - 4.23915954149813403) *
      (4.23915954149813404 - fhbY2Star (2*hplus) * fhbY2Star (2*hplus)) :=
    mul_nonneg (sub_nonneg.mpr hx2b.1) (sub_nonneg.mpr hx2b.2)
  obtain ⟨hd0, hal0, har0⟩ := g3c_slot0 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd1, hal1, har1⟩ := g3c_slot1 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd2, hal2, har2⟩ := g3c_slot2 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd3, hal3, har3⟩ := g3c_slot3 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd4, hal4, har4⟩ := g3c_slot4 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd5, hal5, har5⟩ := g3c_slot5 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd6, hal6, har6⟩ := g3c_slot6 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd7, hal7, har7⟩ := g3c_slot7 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd8, hal8, har8⟩ := g3c_slot8 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd9, hal9, har9⟩ := g3c_slot9 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd10, hal10, har10⟩ := g3c_slot10 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd11, hal11, har11⟩ := g3c_slot11 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd12, hal12, har12⟩ := g3c_slot12 hx2b.1 hx2b.2 hx2prod
  obtain ⟨hd13, hal13, har13⟩ := g3c_slot13 hx2b.1 hx2b.2 hx2prod
  -- S aggregate: S = 2π + Σ 12 slot arctan
  have hpi : (3.14159265358979323846:ℝ) < Real.pi ∧ Real.pi < 3.14159265358979323847 := g4v_pi_bounds
  have hS : (2.1347373894:ℝ) ≤ solY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 + solY (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) 2 + solY 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 + solY 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 ∧
      solY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 + solY (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) 2 + solY 2 2 2 (2*hplus) (fhbY2Star (2*hplus)) 2 + solY 2 (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 ≤ (2.1347373900:ℝ) := by
    simp only [solY]
    constructor
    · rw [hd0, hd2, hd3, hd4, hd5, hd6, hd8, hd9, hd10, hd11, hd12, hd13]
      linarith [hpi.1, hal0, hal2, hal3, hal4, hal5, hal6, hal8, hal9, hal10, hal11, hal12, hal13]
    · rw [hd0, hd2, hd3, hd4, hd5, hd6, hd8, hd9, hd10, hd11, hd12, hd13]
      linarith [hpi.2, har0, har2, har3, har4, har5, har6, har8, har9, har10, har11, har12, har13]
  -- (fhbY2Star (2*hplus)) two-sided bounds via the fhbX2Root square
  have hynn2 : (0:ℝ) ≤ fhbY2Star (2*hplus) := by
    have hb := fhbX2Root_bounds h1lo (le_refl (2*hplus)); unfold fhbY2Star; positivity
  have hroot : (0:ℝ) ≤ fhbX2Root ((2*hplus) * (2*hplus)) := by
    have hb := fhbX2Root_bounds h1lo (le_refl (2*hplus)); linarith [hb.1]
  have hX2 : fhbX2Root ((2*hplus) * (2*hplus))
      = 4 - (511 / 4489) * ((2*hplus)*(2*hplus))
        + (1250 / 4489) * Real.sqrt (fhbD4 ((2*hplus)*(2*hplus))) := by
    have h := hx2
    unfold fhbY2Star at h
    rwa [Real.mul_self_sqrt hroot] at h
  have hy2 : (2.0589219367:ℝ) ≤ fhbY2Star (2*hplus) ∧ fhbY2Star (2*hplus) ≤ (2.0589219368:ℝ) := by
    constructor
    · unfold fhbY2Star
      rw [hX2, hx2e]
      exact Real.le_sqrt_of_sq_le (by nlinarith [hs.1])
    · unfold fhbY2Star
      rw [hX2, hx2e]
      rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2.0589219368)]
      nlinarith [hs.2]
  -- f1 = 0
  have h20 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  have ey1 : (2 * hplus) / 2 = hplus := by ring
  -- f2 bounds
  have hf2eq : lmfun ((fhbY2Star (2*hplus)) / 2) = (h0 - (fhbY2Star (2*hplus)) / 2) / (h0 - 1) :=
    g4w_lmfun_div2_of_le (by have hb := fhbY2Star_mem_box h1lo (le_refl (2*hplus)); linarith [hb.2, hm.2, h20] : (fhbY2Star (2*hplus)) ≤ 2 * h0)
  have hf2 : (0.886688583234:ℝ) ≤ lmfun ((fhbY2Star (2*hplus)) / 2) ∧ lmfun ((fhbY2Star (2*hplus)) / 2) ≤ (0.886688583235:ℝ) := by
    rw [hf2eq]
    have hden : (0:ℝ) < h0 - 1 := by norm_num [h0]
    have h0eq : h0 = 1.26 := by norm_num [h0]
    constructor
    · rw [le_div_iff₀ hden]; nlinarith [h0eq, hy2.2]
    · rw [div_le_iff₀ hden]; nlinarith [h0eq, hy2.1]
  -- D aggregate
  have hD : (5.7932238459:ℝ) ≤
      lmfun ((2*hplus) / 2) * dihY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 + lmfun ((fhbY2Star (2*hplus)) / 2) * dihY (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2*hplus) 2 (fhbY2Star (2*hplus)) +
        lmfun (2 / 2) * dihY 2 (2*hplus) 2 (fhbY2Star (2*hplus)) 2 2 + lmfun (2 / 2) * dihY 2 (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) ∧
      lmfun ((2*hplus) / 2) * dihY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 + lmfun ((fhbY2Star (2*hplus)) / 2) * dihY (fhbY2Star (2*hplus)) 2 (2*hplus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2*hplus) 2 (fhbY2Star (2*hplus)) +
        lmfun (2 / 2) * dihY 2 (2*hplus) 2 (fhbY2Star (2*hplus)) 2 2 + lmfun (2 / 2) * dihY 2 (2*hplus) 2 2 2 (fhbY2Star (2*hplus)) ≤
      (5.7932238462:ℝ) := by
    rw [ey1, g4v_lmfun_hplus]
    rw [show ((2:ℝ) / 2) = 1 by norm_num, g4v_lmfun_one]
    rw [hd1, hd6, hd7, hd8, hd11, hd13]
    constructor
    · nlinarith [hpi.1, hf2.1, hal1, hal6, hal7, hal8, hal11, hal13, mul_nonneg (sub_nonneg.mpr hy2.2) (sub_nonneg.mpr hy2.1)]
    · nlinarith [hpi.2, hf2.2, har1, har6, har7, har8, har11, har13, mul_nonneg (sub_nonneg.mpr hy2.2) (sub_nonneg.mpr hy2.1)]
  -- V bound
  have eV : volY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 =
      Real.sqrt (deltaX ((2*hplus)*(2*hplus)) (fhbY2Star (2*hplus)*fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) / 12 := by
    simp only [volY, volXf]
  have hD1 : (146.27647376628598970:ℝ) ≤ deltaX ((2*hplus)*(2*hplus)) (fhbY2Star (2*hplus)*fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ∧
      deltaX ((2*hplus)*(2*hplus)) (fhbY2Star (2*hplus)*fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ≤ (146.27647376628599120:ℝ) := by
    constructor
    · unfold deltaX; nlinarith [hx2b.1, hx2b.2, hx2prod]
    · unfold deltaX; nlinarith [hx2b.1, hx2b.2, hx2prod]
  have hVs : (12.09448112844391475:ℝ) ≤ Real.sqrt (deltaX ((2*hplus)*(2*hplus)) (fhbY2Star (2*hplus)*fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ∧
      Real.sqrt (deltaX ((2*hplus)*(2*hplus)) (fhbY2Star (2*hplus)*fhbY2Star (2*hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ≤ (12.09448112844391482:ℝ) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [hD1.1])
    · exact (Real.sqrt_le_left (by nlinarith [hD1.1])).mpr (by nlinarith [hD1.2])
  have hVl : (1.007873427370:ℝ) ≤ volY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 := by
    rw [eV]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 12)]
    nlinarith [hVs.1]
  have hVr : volY (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 ≤ (1.007873427371:ℝ) := by
    rw [eV]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 12)]
    nlinarith [hVs.2]
  -- kit assembly
  have hk := g4v_corner_value_bounds (y1 := (2*hplus)) (y2 := (fhbY2Star (2*hplus))) (y3 := (2:ℝ)) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := 1.007873427370) (Vhi := 1.007873427371)
    (Slo := 2.1347373894) (Shi := 2.1347373900)
    (Dlo := 5.7932238459) (Dhi := 5.7932238462)
    (Alo := 0.6443106485) (Ahi := 0.6443107122) (Blo := 0.0647174928) (Bhi := 0.0647175183)
    ⟨hVl, hVr⟩ hS hD
    ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩ ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith [hk.1]
end Kepler.Text

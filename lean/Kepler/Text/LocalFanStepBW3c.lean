/-
Kepler/Text/LocalFanStepBW3c.lean — wave C-W3c：stepB ¬B 缺口支总装 + 收口。

内容：
* `pW3_propagation`：在 stepB 的缺口支上下文（convexLocalFan_p2 + generic +
  违反点 v 的内角 < π + 基包含 `affGt {0}{v,w} ⊆ wedge(v,ρv)`）下，
  `∀ x ∈ FF`（含坏 dart）都有 `affGt {0}{v,w} ⊆ wedgeInFanGt_p2 x E`。
  两臂：`azim 0 x.1 x.2 (ιx.1) = π` → W3a；`< π` → W3b-ii
  （`< π` 由 `hconv x hx` 的 `azimInFan x E ≤ π` + 非 `=π`）。
* `pW3c_gap_contradiction`：`pW1_gap_setup` 的坏 dart 与传播矛盾 ⇒ False。
* `pW3c_angle_ge_pi_of_gap`：¬B 支的直接结论形 `π ≤ interiorAngle1_p2 0 FF v`
  （W7 的 `angle_bound` 槽）。
* `pW3c_sol_nonneg_of_gap`：¬B 支的 `0 ≤ solLocal_p9 E FF` 条件形。

不包含：B 支（W4–W6 u/w 分解）与 k=3 分支（W7）。
-/
import Kepler.Text.LocalFanStepBW3bII

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 本地私有（BW3bII 的 card/azimCycle 是 private） -/

private theorem pW3c_card_EE (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    (EE_p2 x.1 E).ncard = 2 := by
  obtain ⟨hx1V, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hx hx
  exact LOFA_CARD_EE_V_1 h hx1V

private theorem pW3c_azimCycle (h : localFan_p2 V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    azimCycle_p2 (EE_p2 x.1 E) (0 : V3) x.1 x.2 = ivsRhoNode1_p2 FF x.1 := by
  obtain ⟨hx1V, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hx hx
  have hιV : ivsRhoNode1_p2 FF x.1 ∈ V := LOCAL_FAN_IVS_IN_V h hx1V
  have hρ : rhoNode1_p2 FF (ivsRhoNode1_p2 FF x.1) = x.1 :=
    LOCAL_FAN_RHO_NODE_IVS h hx1V
  have hrho2 : rhoNode1_p2 FF x.1 = x.2 := DETER_RHO_NODE h hx
  have hEE : (EE_p2 x.1 E) = ({x.2, ivsRhoNode1_p2 FF x.1} : Set V3) := by
    rw [LOFA_IMP_EE_TWO_ELMS h hιV hρ, hrho2]
  rw [hEE]
  exact AZIM_CYCLE_TWO_POINT_SET x.2 (ivsRhoNode1_p2 FF x.1) (0 : V3) x.1

/-! ## §1 传播：全 dart（W3a + W3b-ii 两臂） -/

/-- **stepB 的传播**：缺口支上下文下，基包含传播到**所有** dart（含坏 dart）。 -/
theorem pW3_propagation
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (haz : azimInFan_p2 (v, rhoNode1_p2 FF v) E < Real.pi)
    (hbase : affGt ({0} : Set V3) {v, w}
      ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E := by
  intro x hx
  have hl : localFan_p2 V E FF := hcl.1
  have hconv := hcl.2
  have heq : azimInFan_p2 x E = azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) := by
    unfold azimInFan_p2
    rw [if_pos (by rw [pW3c_card_EE hl hx]; norm_num), pW3c_azimCycle hl hx]
  have hle : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) ≤ Real.pi := by
    rw [← heq]
    exact (hconv x hx).1
  by_cases hpi : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) = Real.pi
  · exact pW3a_affGt_subset_wedge_pi hcl hg hv hw hvw haz hbase hx hpi
  · exact pW3b_affGt_subset_wedge_lt_pi hcl hg hv hw hvw haz hbase hx
      (lt_of_le_of_ne hle hpi)

/-! ## §2 ¬B 缺口支收口 -/

/-- **¬B 缺口支矛盾**：`pW1_gap_setup` 的坏 dart 与 `pW3_propagation` 直接矛盾。 -/
theorem pW3c_gap_contradiction
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    {v : V3} (hv : v ∈ V) (hk4 : 3 < V.ncard)
    (hint : interiorAngle1_p2 0 FF v < Real.pi)
    (hB : ¬ ∀ i, i < V.ncard →
      azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) = 0 ∨
        azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) =
          azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[V.ncard - 1] v)) :
    False := by
  have hl : localFan_p2 V E FF := hcl.1
  obtain ⟨i, w, -, -, hw, hgt0, -, hbase, e, heFF, hebad⟩ :=
    pW1_gap_setup hcl hg hnc hv hk4 hB
  have hwV : w ∈ V := by
    rw [hw]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hl hv i
  have hvw : v ≠ w := by
    intro hwv
    have hgt0' : 0 < azim 0 v (rhoNode1_p2 FF v) w := hgt0
    rw [show w = v from hwv.symm] at hgt0'
    have h0 : azim 0 v (rhoNode1_p2 FF v) v = 0 := by
      unfold azim
      rw [if_pos (Or.inr (collinear3_pair_right rfl))]
    rw [h0] at hgt0'
    exact lt_irrefl 0 hgt0'
  have haz : azimInFan_p2 (v, rhoNode1_p2 FF v) E < Real.pi := by
    have h := CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_p9 hcl v hv
    rw [← h]
    exact hint
  have hprop := pW3_propagation hcl hg hv hwV hvw haz hbase e heFF
  exact hebad hprop

/-- **¬B 支的直接结论形**（W7 `angle_bound` 槽）：`π ≤ interiorAngle1_p2 0 FF v`。 -/
theorem pW3c_angle_ge_pi_of_gap
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    {v : V3} (hv : v ∈ V) (hk4 : 3 < V.ncard)
    (hB : ¬ ∀ i, i < V.ncard →
      azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) = 0 ∨
        azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) =
          azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[V.ncard - 1] v)) :
    Real.pi ≤ interiorAngle1_p2 0 FF v := by
  by_contra h
  rw [not_le] at h
  exact pW3c_gap_contradiction hcl hg hnc hv hk4 h hB

/-- **¬B 支的 `0 ≤ solLocal_p9` 条件形**。 -/
theorem pW3c_sol_nonneg_of_gap
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    {v : V3} (hv : v ∈ V) (hk4 : 3 < V.ncard)
    (hint : interiorAngle1_p2 0 FF v < Real.pi)
    (hB : ¬ ∀ i, i < V.ncard →
      azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) = 0 ∨
        azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) =
          azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[V.ncard - 1] v)) :
    0 ≤ solLocal_p9 E FF :=
  False.elim (pW3c_gap_contradiction hcl hg hnc hv hk4 hint hB)

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW3_propagation
#print axioms Kepler.Text.pW3_propagation
#check @Kepler.Text.pW3c_gap_contradiction
#print axioms Kepler.Text.pW3c_gap_contradiction
#check @Kepler.Text.pW3c_angle_ge_pi_of_gap
#print axioms Kepler.Text.pW3c_angle_ge_pi_of_gap
#check @Kepler.Text.pW3c_sol_nonneg_of_gap
#print axioms Kepler.Text.pW3c_sol_nonneg_of_gap

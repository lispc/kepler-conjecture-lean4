/-
LocalAuto7W22dI: W22d-i — `CLOSED_WEDGE` 真证（`p22d_closedWedge`）。

HOL 锚：`leaf_cell.hl:3659-3709`（三支）：
* `< π`（:3659 `CLOSED_WEDGE_LT_PI`）= `WEDGE_GE_EQ_AFF_GE` + `CLOSED_AFF_GE`
  ⇒ Lean `WEDGE_GE_EQ_AFF_GE`（LA5:2024，std3）+ `yk10_isClosed_affGe22`
  （TameLp:9968；W22d-i 前置：private→theorem 可见性改动，编排者落）；
* `= π`（:3671 `CLOSED_WEDGE_EQ_PI`）= `AZIM_PI_WEDGE_GE_CROSS_DOT` + 闭半空间；
* `> π`（:3686 支）= `AZIM_SPLIT_POINT` + `WEDGE_GE_SPLIT` + 闭并集。
  `AZIM_SPLIT_POINT` 原为 PA18 未证桩；此处按 HOL 证体（:3612-3658）自证：
  `IN_CONV0_IMP_AZIM_PI`（LA5:7459，std3）+ `IN_CONV0`（LA5:4105，std3）
  给中点 `u0 ∈ conv0_p2 {u2, 2•u0−u2}`；`WEDGE_GE_SPLIT`/`AZIM_BASE_SHIFT_LE`
  为 PA18 的 **std3** 件，本文件**本地移植**（不 import PackingAuto18）。

纪律：不 import PackingAuto18；零禁词；主仓 tracked 零改动。
-/
import Kepler.Text.LocalAuto5
import Kepler.Text.PackingAuto2
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## §0 私件：AZIM_BASE_SHIFT_LE + WEDGE_GE_SPLIT（PA18 std3 件本地移植） -/

/-- HOL `AZIM_BASE_SHIFT_LE`（leaf_cell.hl:3529-3547；PA18:7649 std3）：
两次 `sum4_azim_fan` + 线性算术。 -/
private theorem azimBaseShiftLe (x y b1 b2 w1 w2 : V3)
    (h1 : ¬Collinear3 x y b1) (h2 : ¬Collinear3 x y b2)
    (h3 : ¬Collinear3 x y w1) (h4 : ¬Collinear3 x y w2)
    (h5 : azim x y b1 b2 ≤ azim x y b1 w1)
    (h6 : azim x y b1 b2 ≤ azim x y b1 w2) :
    azim x y b1 w2 - azim x y b1 w1 = azim x y b2 w2 - azim x y b2 w1 := by
  have hyx : y ≠ x := fun he => h1 (collinear3_of_eq he)
  have e1 := sum4_azim_fan hyx h1 h2 h4 h6
  have e2 := sum4_azim_fan hyx h1 h2 h3 h5
  linarith

/-- HOL `WEDGE_GE_SPLIT`（leaf_cell.hl:3548-3611；PA18:7661 std3）：
插入内射线把闭楔形拆成两个闭楔形之并。 -/
private theorem wedgeGeSplit (u0 u1 u2 u3 w : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hw : w ∈ Kepler.Geom.wedge u0 u1 u2 u3) :
    ¬Collinear3 u0 u1 w ∧
      wedgeGe u0 u1 u2 u3 = wedgeGe u0 u1 u2 w ∪ wedgeGe u0 u1 w u3 := by
  rw [Kepler.Geom.wedge, Set.mem_setOf_eq] at hw
  refine ⟨hw.1, ?_⟩
  refine Set.ext (fun x => ?_)
  by_cases hcol : Collinear3 u0 u1 x
  · have hx0 : azim u0 u1 u2 x = 0 := by
      rw [azim, if_pos (Or.inr hcol)]
    constructor
    · intro hx
      refine Set.mem_union_left _ ?_
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
      rw [hx0]
      exact le_of_lt hw.2.1
    · intro hx
      rw [Set.mem_union] at hx
      rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
      rcases hx with hx | hx
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
      · rw [hx0]
        exact ⟨le_refl 0, azim_nonneg u0 u1 u2 u3⟩
  · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle | hgt
    · constructor
      · intro hx
        refine Set.mem_union_left _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        exact ⟨azim_nonneg u0 u1 u2 x, hle⟩
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle (le_of_lt hw.right.right)⟩
    · have hshift := azimBaseShiftLe u0 u1 u2 w x u3 h2 hw.1 hcol h3
        (le_of_lt hgt) (le_of_lt hw.2.2)
      constructor
      · intro hx
        refine Set.mem_union_right _ ?_
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        refine ⟨azim_nonneg u0 u1 w x, ?_⟩
        linarith
      · intro hx
        rw [Set.mem_union] at hx
        rw [wedgeGe, Set.mem_setOf_eq] at hx ⊢
        rcases hx with hx | hx
        · exact ⟨hx.1, le_trans hx.2 (le_of_lt hw.right.right)⟩
        · rcases le_or_gt (azim u0 u1 u2 x) (azim u0 u1 u2 w) with hle'' | hgt''
          · exact ⟨azim_nonneg u0 u1 u2 x, le_trans hle'' (le_of_lt hw.2.2)⟩
          · have hshift' := azimBaseShiftLe u0 u1 u2 w x u3 h2 hw.1 hcol h3
              (le_of_lt hgt'') (le_of_lt hw.2.2)
            rw [wedgeGe, Set.mem_setOf_eq] at hx
            refine ⟨azim_nonneg u0 u1 u2 x, ?_⟩
            linarith

/-! ## §1 三支 -/

/-- `azim < π` 支（HOL `CLOSED_WEDGE_LT_PI`）：`wedgeGe = affGe 2+2`，`affGe 2+2` 闭。 -/
private theorem closedWedgeLtPi {u0 u1 u2 u3 : V3}
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hlt : azim u0 u1 u2 u3 < Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  have h01 : u0 ≠ u1 := fun he => h2 (collinear3_of_eq he.symm)
  have h02 : u2 ≠ u0 := fun he => h2 (collinear3_pair_left he)
  have h03 : u3 ≠ u0 := fun he => h3 (collinear3_pair_left he)
  have h12 : u2 ≠ u1 := fun he => h2 (collinear3_pair_right he)
  have h13 : u3 ≠ u1 := fun he => h3 (collinear3_pair_right he)
  rw [show wedgeGe u0 u1 u2 u3 = Kepler.Text.wedgeGe_p2 u0 u1 u2 u3 from rfl,
    WEDGE_GE_EQ_AFF_GE hlt h2 h3]
  -- HOL `CLOSED_AFF_GE` 无互异前件：`u2 = u3` 时 `{u2,u3}` 塌缩为单点，走 2+1 形。
  by_cases h23 : u2 = u3
  · have hset : affGe ({u0, u1} : Set V3) ({u2, u3} : Set V3)
        = affGe ({u0, u1} : Set V3) ({u2} : Set V3) := by
      rw [← h23]
      simp
    rw [hset]
    exact closed_aff_ge_2_1 h2
  · exact Kepler.Text.TameLp.yk10_isClosed_affGe22 h01 h02 h03 h12 h13 h23

/-- `azim = π` 支（HOL `CLOSED_WEDGE_EQ_PI`）：闭楔形 = 闭半空间。 -/
private theorem closedWedgeEqPi {u0 u1 u2 u3 : V3}
    (h : azim u0 u1 u2 u3 = Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  rw [show wedgeGe u0 u1 u2 u3 = Kepler.Text.wedgeGe_p2 u0 u1 u2 u3 from rfl,
    AZIM_PI_WEDGE_GE_CROSS_DOT h]
  -- 法向点积对 `x` 连续（TopologyFan `isClosed_dot_ge_zero` 同款显式链）。
  have hcont : Continuous fun x : V3 =>
      (WithLp.toLp 2 (crossProduct ((u1 - u0 : V3) : Fin 3 → ℝ)
        ((u2 - u0 : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (x - u0) := by
    have hc : Continuous fun x : V3 => inner ℝ
        (WithLp.toLp 2 (crossProduct ((u1 - u0 : V3) : Fin 3 → ℝ)
          ((u2 - u0 : V3) : Fin 3 → ℝ)) : V3) (x - u0) :=
      continuous_const.inner (continuous_id.sub continuous_const)
    simpa only [inner_eq_dot, WithLp.ofLp_sub] using hc
  exact isClosed_Ici.preimage hcont

/-- `azim > π` 支的内射线（HOL `AZIM_SPLIT_POINT`，leaf_cell.hl:3612-3658）：
取 `w = 2•u0 − u2`（`u0` 是中点 ⇒ `azim u0 u1 u2 w = π`）。 -/
private theorem azimSplitPoint (u0 u1 u2 u3 : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hgt : Real.pi < azim u0 u1 u2 u3) :
    ∃ w : V3, w ∈ Kepler.Geom.wedge u0 u1 u2 u3 ∧
      azim u0 u1 u2 w = Real.pi ∧ azim u0 u1 w u3 < Real.pi := by
  -- 中点：u0 ∈ conv0_p2 {u2, w}（w = 2•u0 − u2）
  have hmid0 : (1 / (1 + 1 : ℝ)) •
      ((1 : ℝ) • u2 + (1 : ℝ) • ((2 : ℝ) • u0 - u2))
      ∈ conv0_p2 ({u2, (2 : ℝ) • u0 - u2} : Set V3) :=
    IN_CONV0 (x := u2) (y := (2 : ℝ) • u0 - u2) (a := 1) (b := 1)
      (by norm_num) (by norm_num)
  have hmidEq : (1 / (1 + 1 : ℝ)) •
      ((1 : ℝ) • u2 + (1 : ℝ) • ((2 : ℝ) • u0 - u2)) = u0 := by
    rw [show (1 : ℝ) / (1 + 1) = 1 / 2 from by norm_num, one_smul, one_smul]
    module
  rw [hmidEq] at hmid0
  -- hcol：{u0,u2,u1} 非共线（h2 重排）
  have hcol : ¬ Collinear ℝ ({u0, u2, u1} : Set V3) := by
    intro hc
    have hset : ({u0, u2, u1} : Set V3) = ({u0, u1, u2} : Set V3) := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hc' : Collinear ℝ ({u0, u1, u2} : Set V3) := hset ▸ hc
    exact h2 hc'
  have hazim : azim u0 u1 u2 ((2 : ℝ) • u0 - u2) = Real.pi :=
    IN_CONV0_IMP_AZIM_PI (x := u0) (a := u2) (b := (2 : ℝ) • u0 - u2) (e := u1)
      hcol hmid0
  -- w 不在轴上（否则 azim = 0 ≠ π）
  have hwcol : ¬ Collinear3 u0 u1 ((2 : ℝ) • u0 - u2) := by
    intro hc
    have h0 : azim u0 u1 u2 ((2 : ℝ) • u0 - u2) = 0 := by
      unfold azim
      rw [if_pos (Or.inr hc)]
    rw [hazim] at h0
    exact Real.pi_ne_zero h0
  refine ⟨(2 : ℝ) • u0 - u2, ⟨hwcol, ?_, ?_⟩, hazim, ?_⟩
  · rw [hazim]
    exact Real.pi_pos
  · rw [hazim]
    exact hgt
  · -- sum4_azim_fan：azim u0 u1 w u3 = azim u0 u1 u2 u3 − π < π（AZIM_RANGE）
    have hyx : u1 ≠ u0 := fun he => h2 (by rw [he]; exact collinear3_of_eq rfl)
    have hle : azim u0 u1 u2 ((2 : ℝ) • u0 - u2) ≤ azim u0 u1 u2 u3 := by
      rw [hazim]
      exact le_of_lt hgt
    have hsum := sum4_azim_fan hyx h2 hwcol h3 hle
    rw [hazim] at hsum
    have hr := (AZIM_RANGE u0 u1 u2 u3).2
    linarith

/-! ## §2 HOL `CLOSED_WEDGE`（PA18:7871 逐字形） -/

/-- **HOL `CLOSED_WEDGE`**（leaf_cell.hl:3686-3709；PA18:7871 陈述逐字）：
闭楔形在两条非共线前提下闭。 -/
theorem p22d_closedWedge (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) : IsClosed (wedgeGe u0 u1 u2 u3) := by
  rcases lt_trichotomy (azim u0 u1 u2 u3) Real.pi with hlt | heq | hgt
  · exact closedWedgeLtPi h2 h3 hlt
  · exact closedWedgeEqPi heq
  · obtain ⟨w, hwmem, hazim, hlt2⟩ := azimSplitPoint u0 u1 u2 u3 h2 h3 hgt
    obtain ⟨hwcol, hsplit⟩ := wedgeGeSplit u0 u1 u2 u3 w h2 h3 hwmem
    rw [hsplit]
    exact (closedWedgeEqPi hazim).union (closedWedgeLtPi hwcol h3 hlt2)

/-! ## `#print axioms` 探针（编译即执行；预期标准三、零 sorryAx） -/

#print axioms closedWedgeLtPi
#print axioms closedWedgeEqPi
#print axioms azimSplitPoint
#print axioms Kepler.Text.p22d_closedWedge

end Kepler.Text

/-
LocalAuto7W13E: W13e — WSEWPCH straight 支的 perimeter 换位组装
（HOL polar_fan.hl:2758-2800 的 `DISJ_CASES_TAC (CARD V' <= 2 \/ 3 <= CARD V')` 两子支）。

## 接口（WSEWPCH_final straight 支直接可呼）

* `p13e_fanPerimeter_setSum`：`fanPerimeter V E FF = setSum V' (arcV 0 w (r w))`
  —— **不需要新扇的 `LocalFan`**（HOL 2712 的 `SUBGOAL_THEN ... SUBST1_TAC` 形状），
  故 `V'.ncard ≤ 2` 子支也能用（该支无 `hcard3`，`p13d_fanPerimeter` 不可用）；
* `p13e_setSum_arcV_le_two_pi`：`s.ncard ≤ 2 ⇒ setSum s (arcV 0 w (r w)) ≤ 2π`
  （HOL 2759-2765：每项 `arcV ≤ π`，项数 ≤ 2）；
* `p13e_straight_perimeter`：**两子支合一的换位收口**——IH 取「所有更小扇」形
  （强归纳的直接形态），`V'.ncard ≤ 2` 走上界、`3 ≤ V'.ncard` 走
  `p13d_fanPerimeter` + `p13a_convex` + `p12b_card_lt` 递归；
* `p13e_straight_perimeter_of_not_generic`：straight 支入口——`¬(∀ v, interiorAngle1 < π)`
  + 凸性上界 ⇒ `∃ v, interiorAngle1 = π`，再交上件（HOL 2625-2634 的
  `NOT_FORALL_THM` + `CONVEX_LOFA_IMP_INANGLE_LE_PI`）。

## 同批可见性改动（W13D，4 行，陈述零改）

`p13d_arcV_eq_angle` / `p13d_setSum_congr` / `p13d_setSum_insert` /
`p13d_affGt_of_affGe`：`private theorem` → `theorem`（`p13e_fanPerimeter_setSum` 复用，
避免 ~70 行重证；先例 W13B 两件 / AQ12 `12I`）。

W13A–D / W12E–P / LA7 零改动；**无新增 import**。
-/
import Kepler.Text.LocalAuto7W13D

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 1. `fanPerimeter` 的 `setSum` 形（不需新扇 `LocalFan`；HOL 2712） -/

/-- **`fanPerimeter V E FF = setSum V' (arcV 0 w (r w))`**：与 `p13d_fanPerimeter`
同一条 sum 重组（`V = insert v V'`、`V' = insert ιv (V'\{ιv})`、差集逐点 `r = ρ`、
`ANGLES_ADD_AFF_GE`），但 **RHS 直接写成 `setSum`**，故不需要 `hcard3`
（`V'.ncard ≤ 2` 子支唯一可用形）。 -/
theorem p13e_fanPerimeter_setSum {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    fanPerimeter V E FF
      = setSum (p12b_V V v) (fun w => arcV 0 w (p12b_R FF v w)) := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hVfin : (p12b_V V v).Finite := (p12b_card hcl hv).1
  have hιV : ivsRhoNode1 FF v ∈ V := LOCAL_FAN_IVS_IN_V h2 hv
  have hιV' : ivsRhoNode1 FF v ∈ p12b_V V v := ⟨hιV, IVS_RHO_NODE_DIFF_ID h2 hv⟩
  have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
  rw [FAN_PERIMETER hcl.1 hedge]
  have hV : V = insert v (p12b_V V v) := by
    ext x
    constructor
    · intro hx
      by_cases hxv : x = v
      · exact hxv ▸ Set.mem_insert _ _
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, by simpa using hxv⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact hv
      · exact hx'.1
  have hV' : p12b_V V v = insert (ivsRhoNode1 FF v) (p12b_V V v \ {ivsRhoNode1 FF v}) := by
    rw [Set.insert_sdiff_singleton]
    exact (Set.insert_eq_of_mem hιV').symm
  have hv_not : v ∉ insert (ivsRhoNode1 FF v) (p12b_V V v \ {ivsRhoNode1 FF v}) := by
    intro h
    rcases Set.mem_insert_iff.mp h with h1 | h1
    · exact (IVS_RHO_NODE_DIFF_ID h2 hv) h1.symm
    · exact h1.1.2 (by simp)
  conv_lhs => rw [hV]
  rw [hV']
  rw [p13d_setSum_insert _ hv_not (hVfin.sdiff.insert _)]
  rw [p13d_setSum_insert _ (by simp) hVfin.sdiff]
  rw [p13d_setSum_insert _ (by simp) hVfin.sdiff]
  have hcongr : setSum (p12b_V V v \ {ivsRhoNode1 FF v}) (fun w => arcV 0 w (rhoNode1 FF w))
      = setSum (p12b_V V v \ {ivsRhoNode1 FF v}) (fun w => arcV 0 w (p12b_R FF v w)) :=
    p13d_setSum_congr (fun w hw => by
      rw [p13c_R_eq_rho_of_ne hcl hedge hw.1 (by simpa using hw.2)])
  rw [hcongr]
  have hρv : rhoNode1 FF (ivsRhoNode1 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h2 hv
  have hrv : p12b_R FF v (ivsRhoNode1 FF v) = rhoNode1 FF v := by
    unfold p12b_R
    rw [show rhoNode1 FF (ivsRhoNode1 FF v) = v from hρv]
    exact if_pos rfl
  rw [hρv, hrv]
  have hι0 : ivsRhoNode1 FF v ≠ 0 := fun h => h0V (h ▸ hιV)
  have hρ0 : rhoNode1 FF v ≠ 0 :=
    fun h => h0V (h ▸ LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv)
  have hv0 : v ≠ 0 := fun h => h0V (h ▸ hv)
  have hιρ : ivsRhoNode1 FF v ≠ rhoNode1 FF v := by
    intro h
    have h1 : rhoNode1 FF (ivsRhoNode1 FF v) = rhoNode1 FF (rhoNode1 FF v) := by rw [h]
    rw [hρv] at h1
    exact LOCAL_FAN_IMP_NOT_SEMI_IDE h2 hv h1.symm
  have hgt : v ∈ affGt ({0} : Set V3) ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) :=
    p13d_affGt_of_affGe hι0 hρ0 hιρ (p12b_straight_mem hcl hedge hg hv hpi)
      (LOFA_IMP_NOT_COLL_IVS h2 hv) (LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv)
  have hangle : arcV 0 (ivsRhoNode1 FF v) v + arcV 0 v (rhoNode1 FF v)
      = arcV 0 (ivsRhoNode1 FF v) (rhoNode1 FF v) := by
    rw [p13d_arcV_eq_angle, p13d_arcV_eq_angle, p13d_arcV_eq_angle]
    exact ANGLES_ADD_AFF_GE hι0 hρ0 hv0 hgt
  linarith [hangle]

/-! ## 2. `V'.ncard ≤ 2` 子支的上界（HOL 2759-2765） -/

/-- **`s.ncard ≤ 2 ⇒ setSum s (arcV 0 w (r w)) ≤ 2π`**：每项 `arcV ≤ π`
（`Real.arccos_le_pi`），项数 ≤ 2。 -/
theorem p13e_setSum_arcV_le_two_pi {s : Set V3} {r : V3 → V3}
    (hs : s.Finite) (hcard : s.ncard ≤ 2) :
    setSum s (fun w => arcV 0 w (r w)) ≤ 2 * Real.pi := by
  rw [setSum, dif_pos hs]
  have hcard' : hs.toFinset.card ≤ 2 := by
    rw [← Set.ncard_eq_toFinset_card s hs]
    exact hcard
  have h1 : ∑ w ∈ hs.toFinset, arcV 0 w (r w) ≤ hs.toFinset.card • Real.pi :=
    Finset.sum_le_card_nsmul _ _ _ (fun w _ => Real.arccos_le_pi _)
  rw [nsmul_eq_mul] at h1
  have h2 : (hs.toFinset.card : ℝ) * Real.pi ≤ 2 * Real.pi := by
    have h3 : (hs.toFinset.card : ℝ) ≤ 2 := by exact_mod_cast hcard'
    nlinarith [Real.pi_pos]
  linarith

/-! ## 3. straight 支 perimeter 换位收口（两子支合一） -/

/-- **straight 支 `fanPerimeter V E FF ≤ 2π`**（HOL 2758-2800 两子支合一）。
`hIH` 是「所有更小扇」形强归纳假设（`U.ncard < V.ncard`）：

* `V'.ncard ≤ 2`：`p13e_fanPerimeter_setSum` + `p13e_setSum_arcV_le_two_pi`；
* `3 ≤ V'.ncard`：`p13d_fanPerimeter` 换到 `fanPerimeter V' E' FF'`，再用
  `p13a_convex`（凸性）+ `p12b_card_lt`（测度下降）+ hedge' 交 `hIH`。 -/
theorem p13e_straight_perimeter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hIH : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      U.ncard < V.ncard → ConvexLocalFan U E' g → (∀ v ∈ U, ∃ w, {v, w} ∈ E') →
        fanPerimeter U E' g ≤ 2 * Real.pi)
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  have hVfin : (p12b_V V v).Finite := (p12b_card hcl hv).1
  rw [p13e_fanPerimeter_setSum hcl hedge hg hv hpi]
  by_cases hsmall : (p12b_V V v).ncard ≤ 2
  · exact p13e_setSum_arcV_le_two_pi hVfin hsmall
  · have hcard3 : 3 ≤ (p12b_V V v).ncard := by omega
    have hne : (p12b_V V v).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h] at hcard3
      simp at hcard3
    obtain ⟨w0, hw0⟩ := hne
    have hlf' : LocalFan (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) :=
      p12p_LocalFan hcl hedge hg hv hpi hcard hw0 hcard3
    have hedge' : ∀ x ∈ p12b_V V v, ∃ y, {x, y} ∈ p12b_E V FF v :=
      fun x hx => ⟨p12b_R FF v x, x, hx, rfl⟩
    have heq : setSum (p12b_V V v) (fun w => arcV 0 w (p12b_R FF v w))
        = fanPerimeter (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) := by
      rw [FAN_PERIMETER hlf' hedge']
      exact p13d_setSum_congr (fun w hw => by rw [(p12b_rho_FF hw).symm])
    rw [heq]
    exact hIH (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) (p12b_card_lt hcl hv)
      (p13a_convex hcl hedge hg hv hw0 hpi hcard hcard3) hedge'

/-! ## 4. straight 支入口（HOL 2625-2634 的 `NOT_FORALL_THM` + 凸性上界） -/

/-- **straight 支入口**：`¬(∀ v ∈ V, interiorAngle1 0 FF v < π)` 在凸扇上等价于
`∃ v ∈ V, interiorAngle1 0 FF v = π`（凸性给 `≤ π`，`NOT_FORALL` 给 `≥ π`），
再交 `p13e_straight_perimeter`。 -/
theorem p13e_straight_perimeter_of_not_generic {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)}
    (hIH : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      U.ncard < V.ncard → ConvexLocalFan U E' g → (∀ v ∈ U, ∃ w, {v, w} ∈ E') →
        fanPerimeter U E' g ≤ 2 * Real.pi)
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) (hcard : 3 ≤ V.ncard)
    (hng : ¬ ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi) :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  have hcvx2 : convexLocalFan_p2 V E FF := p13w_convexLocalFan_p2_of_clf hcl
  rw [not_forall] at hng
  obtain ⟨v, hng'⟩ := hng
  rw [Classical.not_imp] at hng'
  obtain ⟨hv, hge⟩ := hng'
  have hle : interiorAngle1 (0 : V3) FF v ≤ Real.pi :=
    CONVEX_LOFA_IMP_INANGLE_LE_PI hcvx2 hv
  exact p13e_straight_perimeter hIH hcl hedge hg hv (le_antisymm hle (not_lt.mp hge)) hcard

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p13e_fanPerimeter_setSum
#print axioms Kepler.Text.p13e_setSum_arcV_le_two_pi
#print axioms Kepler.Text.p13e_straight_perimeter
#print axioms Kepler.Text.p13e_straight_perimeter_of_not_generic

end Kepler.Text

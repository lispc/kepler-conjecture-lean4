/-
Kepler/Text/LocalFanStepBW1.lean — wave C-W1（B 段）：stepB 的缺口索引与缺口支设置。

范围（严格 B 段，HOL NKEZBFC.hl:1768-1817）：
* 反设内角 < π，定义 `vv i = ρ^[i]v`、`bta i = azim 0 v (vv 1) (vv i)`、`k = V.ncard`；
* 经典二分 `B := ∀ i<k, bta i = 0 ∨ bta i = bta(k-1)`；
* `¬B` 给出缺口索引 `i`，并用 EGHNAVX 的单调性/非负性得到 `0 < bta i < bta(k-1)`。

不包含 C 段（基 dart 切片包含）、D/E（中间角/求和坍缩）与 B 支收口；它们
分别在 W2/W3 与本文件的后续批次。接口 `angle_bound_gt` 见
`WAVE_C_STEPB_PLAN.md` §10.2。
-/
import Kepler.Text.LocalFanStepB

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **B 段缺口索引**：在 `¬B`（存在某个 i 的 bta 既非 0 也非 last）下，
EGHNAVX 给出 `i < k-1` 且 `0 < bta i < bta(k-1)`。 -/
theorem pW1_gap_index
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hk4 : 3 < k)
    (hcol : ∀ w ∈ V, w ≠ v → ¬ Collinear ℝ ({0, v, w} : Set V3))
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    (hB : ¬ ∀ i, i < k → bta i = 0 ∨ bta i = bta (k - 1)) :
    ∃ i : ℕ, i < k - 1 ∧ 0 < bta i ∧ bta i < bta (k - 1) := by
  have hegh := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hv hk hcol hiter hbta
  obtain ⟨-, -, hmono, -⟩ := hegh
  obtain ⟨i, hi⟩ := not_forall.mp hB
  obtain ⟨hik, hi'⟩ := Classical.not_imp.mp hi
  have hi0 : bta i ≠ 0 := fun h => hi' (Or.inl h)
  have hilast : bta i ≠ bta (k - 1) := fun h => hi' (Or.inr h)
  have hkm1 : k - 1 < k := by omega
  have hikm1 : i < k - 1 := by
    rcases lt_or_ge i (k - 1) with h | h
    · exact h
    · exfalso
      have hik' : i = k - 1 := by omega
      exact hilast (by rw [hik'])
  have hile : bta i ≤ bta (k - 1) := hmono i (k - 1) hikm1 hkm1
  have h0le : 0 ≤ bta i := by
    rw [← hbta i]
    exact azim_nonneg _ _ _ _
  exact ⟨i, hikm1, lt_of_le_of_ne' h0le hi0, lt_of_le_of_ne hile hilast⟩

/-- **C 段基 dart 切片包含**：`affGt {0}{v,w} ⊆ wedge_in_fan_gt (v,ρv) E`
（HOL NKEZBFC.hl:1832-1860）。输入：`w∈V`、`0,v,w` 非共线、`bta i = azim 0 v (ρv) w`
严格落在 `0` 与 `azim 0 v (ρv) (ιv)` 之间。 -/
theorem pW1_base_incl
    (hcl : convexLocalFan_p2 V E FF) {v w : V3} (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hnc0 : ¬ Collinear ℝ ({0, v, w} : Set V3))
    (hgt0 : 0 < azim 0 v (rhoNode1_p2 FF v) w)
    (hgtk : azim 0 v (rhoNode1_p2 FF v) w
      < azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)) :
    affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E := by
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have h0v : (0 : V3) ≠ v := fun h => h0V (h ▸ hv)
  have hw0 : w ≠ 0 := fun h => h0V (h ▸ hw)
  have hρnc : ¬ Collinear3 (0 : V3) v (rhoNode1_p2 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hcl.1 hv
  have hι : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hcl.1 hv
  have hρι : rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := LOCAL_FAN_RHO_NODE_IVS hcl.1 hv
  have hEE : EE_p2 v E = {rhoNode1_p2 FF v, ivsRhoNode1_p2 FF v} :=
    LOFA_IMP_EE_TWO_ELMS hcl.1 hι hρι
  have hcard : 1 < (EE_p2 v E).ncard := by
    rw [LOFA_CARD_EE_V_1 hcl.1 hv]; norm_num
  have hcyc : azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v) = ivsRhoNode1_p2 FF v := by
    rw [hEE]
    exact AZIM_CYCLE_TWO_POINT_SET _ _ _ _
  unfold wedgeInFanGt_p2
  rw [if_pos hcard, hcyc]
  rw [aff_gt_inter_aff_gt (x := (0 : V3)) (v := v) (w := w) hnc0]
  intro x hx
  have hxA : x ∈ affGt ({0, v} : Set V3) {w} := hx.1
  obtain ⟨c, hc0, h, hxeq⟩ :=
    (affGt_pair_iff (v0 := (0 : V3)) (v1 := v) (x := w) (y := x) h0v hw0 (Ne.symm hvw)).mp hxA
  have hxeq' : x = c • w + h • v := by simpa using hxeq
  have hxcombo : x = (1 - h - c) • (0 : V3) + h • v + c • w := by
    rw [hxeq']
    module
  have haz : azim 0 v (rhoNode1_p2 FF v) w = azim 0 v (rhoNode1_p2 FF v) x :=
    azim_of_affGt_combo hρnc hnc0 (1 - h - c) h c hc0 (by ring) hxcombo
  refine ⟨?_, ?_, ?_⟩
  · exact aff_gt_imp_not_collinear hnc0 hxA
  · rw [← haz]; exact hgt0
  · rw [← haz]; exact hgtk

/-- `azim 0 v (ρv) (ιv) = bta(k-1)`（HOL NKEZBFC.hl:1864）。 -/
theorem pW1_azim_last
    (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ} (hk : V.ncard = k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i) :
    azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) = bta (k - 1) := by
  have h1 : vv 1 = rhoNode1_p2 FF v := by
    rw [← hiter 1]
    simp
  have h2 : vv (k - 1) = ivsRhoNode1_p2 FF v := by
    rw [← hiter (k - 1)]
    have hk1 : k - 1 = V.ncard - 1 := by omega
    rw [hk1]
    exact ITER_CARD_MINUS1_EQ_IVS_RN1 h hv
  rw [← hbta (k - 1), h1, h2]

/-- **W1 汇总（缺口支）**：在 `¬B` 下，从违反点 `v`（`interior < π`）产出缺口索引
`i`、弦端点 `w = ρ^[i]v`、缺口不等式、基 dart 切片包含、以及 `¬chord` 给出的坏 dart
`e ∈ FF`。 -/
theorem pW1_gap_setup
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)
    {v : V3} (hv : v ∈ V)
    (hk4 : 3 < V.ncard)
    (hB : ¬ ∀ i, i < V.ncard →
      azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) = 0 ∨
        azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[i] v) =
          azim 0 v ((rhoNode1_p2 FF)^[1] v) ((rhoNode1_p2 FF)^[V.ncard - 1] v)) :
    ∃ (i : ℕ) (w : V3),
      0 < i ∧ i < V.ncard ∧ w = (rhoNode1_p2 FF)^[i] v ∧
      0 < azim 0 v (rhoNode1_p2 FF v) w ∧
      azim 0 v (rhoNode1_p2 FF v) w
        < azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) ∧
      affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E ∧
      (∃ e ∈ FF, ¬(affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E)) := by
  have h : localFan_p2 V E FF := hcl.1
  let vv : ℕ → V3 := fun i => (rhoNode1_p2 FF)^[i] v
  let bta : ℕ → ℝ := fun i => azim 0 v (vv 1) (vv i)
  have hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i := fun _ => rfl
  have hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i := fun _ => rfl
  have hcol : ∀ w ∈ V, w ≠ v → ¬ Collinear ℝ ({0, v, w} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 h (fun _ _ => trivial) hg v hv
  have hbta0 : bta 0 = 0 := by
    rw [← hbta 0]
    have hv0 : vv 0 = v := by rw [← hiter 0]; simp
    rw [hv0]
    unfold azim
    rw [if_pos (Or.inr (collinear3_pair_right (v0 := (0 : V3)) (v1 := v) rfl))]
  obtain ⟨i, hikm1, hi0, hilt⟩ :=
    pW1_gap_index hcl hv (k := V.ncard) rfl hk4 hcol hiter hbta hB
  have hi_pos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | hp
    · exfalso
      have hz : bta i = 0 := by rw [h0]; exact hbta0
      linarith
    · exact hp
  have hik : i < V.ncard := by omega
  refine ⟨i, vv i, hi_pos, hik, rfl, ?_, ?_, ?_, ?_⟩
  · have hv1 : vv 1 = rhoNode1_p2 FF v := by
      rw [← hiter 1]; simp
    have hbi : azim 0 v (rhoNode1_p2 FF v) (vv i) = bta i := by
      rw [← hv1]
    rw [hbi]; exact hi0
  · have hv1 : vv 1 = rhoNode1_p2 FF v := by
      rw [← hiter 1]; simp
    have hbi : azim 0 v (rhoNode1_p2 FF v) (vv i) = bta i := by
      rw [← hv1]
    have hlast := pW1_azim_last h hv (k := V.ncard) rfl hiter hbta
    rw [hbi, hlast]; exact hilt
  · have hwV : vv i ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i
    have hwv : vv i ≠ v := by
      intro hcon
      have h0lt : 0 < V.ncard := by omega
      have heq : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[0] v := by
        simpa using hcon
      have hiz := LT_CARD_MONO_LOFA h hv i 0 ⟨hik, h0lt, heq⟩
      have hz : bta i = 0 := by rw [hiz]; exact hbta0
      linarith
    have hnc0 : ¬ Collinear ℝ ({0, v, vv i} : Set V3) := hcol (vv i) hwV hwv
    have hv1 : vv 1 = rhoNode1_p2 FF v := by
      rw [← hiter 1]; simp
    have hbi : azim 0 v (rhoNode1_p2 FF v) (vv i) = bta i := by
      rw [← hv1]
    have hlast := pW1_azim_last h hv (k := V.ncard) rfl hiter hbta
    exact pW1_base_incl hcl hv hwV (Ne.symm hwv) hnc0 (by rw [hbi]; exact hi0)
      (by rw [hbi, hlast]; exact hilt)
  · have hwV : vv i ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i
    have hnot : ¬ ∀ e ∈ FF,
        affGt ({0} : Set V3) {v, vv i} ⊆ wedgeInFanGt_p2 e E := by
      intro hall
      exact hnc ⟨v, vv i, hv, hwV, hall⟩
    obtain ⟨e, he⟩ := not_forall.mp hnot
    obtain ⟨heFF, heincl⟩ := Classical.not_imp.mp he
    exact ⟨e, heFF, heincl⟩

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW1_gap_index
#print axioms Kepler.Text.pW1_base_incl
#print axioms Kepler.Text.pW1_azim_last
#print axioms Kepler.Text.pW1_gap_setup

/-
LocalAuto7W13D: W13c — straight 支 `fanPerimeter V E FF = fanPerimeter V' E' FF'`
（HOL polar_fan.hl:2711-2760）。

主线（HOL 逐段）：

1. 两边 `FAN_PERIMETER` 展开成 `setSum`（旧扇 `ρ`，新扇 `ρ_{FF'} = r`，`p12b_rho_FF`）；
2. `V = insert v V'` 提出 `arcV 0 v (ρv)`；`V' = insert ιv (V' \ {ιv})` 提出
   `arcV 0 ιv (ρ ιv)` / `arcV 0 ιv (r ιv)`；
3. 差集 `V' \ {ιv}` 上逐点相等：`w ≠ ιv ⇒ r w = ρw`（`p13c_R_eq_rho_of_ne`）；
4. 唯一实质项 `arcV 0 ιv (ρ ιv) + arcV 0 v (ρv) = arcV 0 ιv (r ιv)`
   = `arcV 0 ιv v + arcV 0 v (ρv) = arcV 0 ιv (ρv)`（`ρ(ιv) = v`、`r ιv = ρv`），
   由 `ANGLES_ADD_AFF_GE` 给：需要 `v ∈ affGt {0}{ιv, ρv}`，由 `p12b_straight_mem`
   （`affGe`）+ 两非共线把两个系数抬成严格正（`p13d_affGt_of_affGe`）。

件表：`p13c_R_eq_rho_of_ne`（W13c 前置）/ `p13d_arcV_eq_angle` / `p13d_setSum_congr` /
`p13d_setSum_insert` / `p13d_affGt_of_affGe` / `p13d_fanPerimeter`。
W13A–C / W12E–P / LA7 零改动；**无新增 import**。
-/
import Kepler.Text.LocalAuto7W13C

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## W13c 前置：`w ≠ ιv ⇒ r w = ρw`（A7 第 4 步） -/

/-- **`p12b_R FF v w = rhoNode1 FF w`**（`w ≠ ιv` 时 `r` 与 `ρ` 重合）：
`ρw = v` 会经 `IVS_RHO_IDD` 反推出 `w = ιv`。 -/
theorem p13c_R_eq_rho_of_ne {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} {w : V3} (hw : w ∈ p12b_V V v)
    (hne : w ≠ ivsRhoNode1 FF v) :
    p12b_R FF v w = rhoNode1 FF w := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  unfold p12b_R
  by_cases hc : rhoNode1 FF w = v
  · rw [if_pos hc]
    exact absurd (by
      have hid : ivsRhoNode1 FF (rhoNode1 FF w) = w := IVS_RHO_IDD h2 hw.1
      rw [hc] at hid
      exact hid.symm) hne
  · rw [if_neg hc]

/-! ## `arcV` ↔ `angle` 与 `setSum` 小工具 -/

/-- `arcV u v w` 是顶点 `u` 处的欧氏角（HOL `ARCV_ANGLE`；`p7_arcV_eq_angle` 的本地副本）。 -/
private theorem p13d_arcV_eq_angle (u v w : V3) :
    arcV u v w = EuclideanGeometry.angle v u w := by
  rw [arcV, EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle,
    inner_eq_dot, ← dist_eq_norm, ← dist_eq_norm]
  simp only [WithLp.ofLp_sub]

/-- `setSum` 逐点相等。 -/
private theorem p13d_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ v ∈ s, f v = g v) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : s.Finite
  · rw [dif_pos hs, dif_pos hs]
    exact Finset.sum_congr rfl fun v hv => h v ((Set.Finite.mem_toFinset hs).mp hv)
  · rw [dif_neg hs, dif_neg hs]

/-- `setSum (insert a s) f = f a + setSum s f`（`a ∉ s`、`s` 有限）。 -/
private theorem p13d_setSum_insert {α : Type*} [DecidableEq α] {s : Set α} {a : α}
    (f : α → ℝ) (ha : a ∉ s) (hs : s.Finite) :
    setSum (insert a s) f = f a + setSum s f := by
  unfold setSum
  rw [dif_pos (hs.insert a), dif_pos hs]
  have hins : (hs.insert a).toFinset = insert a hs.toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Finset.mem_insert]
  rw [hins, Finset.sum_insert]
  rw [Set.Finite.mem_toFinset]
  exact ha

/-! ## `affGe → affGt`：把 `p12b_straight_mem` 的两个非负系数抬成严格正 -/

/-- `Collinear3` 的第三、二点交换（本地副本）。 -/
private theorem p13d_collinear3_comm {a b c : V3} (h : Collinear3 a c b) :
    Collinear3 a b c := by
  unfold Collinear3 at h ⊢
  rwa [show ({a, b, c} : Set V3) = {a, c, b} from by rw [Set.pair_comm b c]]

/-- **`affGe {0}{p,q} → affGt {0}{p,q}`**（两非共线前提把 `p`、`q` 的系数抬成严格正）：
`v = r•p + s•q`（`r,s ≥ 0`）中若 `r = 0` 则 `v ∥ q` 撞 `¬Collinear3 0 v q`，
`s = 0` 对称撞 `¬Collinear3 0 v p`；严格正后按 `Affsign` 显式给见证。 -/
private theorem p13d_affGt_of_affGe {p q y : V3} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q)
    (hmem : y ∈ affGe ({0} : Set V3) ({p, q} : Set V3))
    (hncp : ¬ Collinear3 (0 : V3) y p) (hncq : ¬ Collinear3 (0 : V3) y q) :
    y ∈ affGt ({0} : Set V3) ({p, q} : Set V3) := by
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hmem
  obtain ⟨f, hfin, hvec, hsgn, hone⟩ := hmem
  rw [sum_insert_pair_v (f := f) hfin hp0.symm hq0.symm hpq] at hvec
  have hrep : y = f p • p + f q • q := by
    rw [hvec]; simp
  have hfp0 : 0 ≤ f p := hsgn p (by simp)
  have hfq0 : 0 ≤ f q := hsgn q (by simp)
  have hfp : 0 < f p := by
    rcases lt_or_eq_of_le hfp0 with h | h
    · exact h
    · exfalso
      apply hncq
      refine p13d_collinear3_comm ?_
      rw [show y = f q • q from by rw [hrep, ← h, zero_smul, zero_add]]
      exact (collinear3_iff_smul hq0).mpr ⟨f q, by simp⟩
  have hfq : 0 < f q := by
    rcases lt_or_eq_of_le hfq0 with h | h
    · exact h
    · exfalso
      apply hncp
      refine p13d_collinear3_comm ?_
      rw [show y = f p • p from by rw [hrep, ← h, zero_smul, add_zero]]
      exact (collinear3_iff_smul hp0).mpr ⟨f p, by simp⟩
  refine ⟨fun z => if z = p then f p else if z = q then f q else 1 - f p - f q,
    hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_pair_v (f := fun z => if z = p then f p else if z = q then f q
      else 1 - f p - f q) hfin hp0.symm hq0.symm hpq, hrep]
    simp [Ne.symm hp0, Ne.symm hq0, Ne.symm hpq]
  · intro z hz
    rcases hz with hz | hz
    · subst hz
      simpa using hfp
    · rw [Set.mem_singleton_iff.mp hz]
      simpa [Ne.symm hpq] using hfq
  · rw [sum_insert_pair_s (f := fun z => if z = p then f p else if z = q then f q
      else 1 - f p - f q) hfin hp0.symm hq0.symm hpq]
    simp [Ne.symm hp0, Ne.symm hq0, Ne.symm hpq]
    ring

/-! ## 主件：`fanPerimeter` 删 straight 点不变（HOL 2711-2760） -/

/-- **`fanPerimeter V E FF = fanPerimeter V' E' FF'`**。 -/
theorem p13d_fanPerimeter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    fanPerimeter V E FF = fanPerimeter (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hVfin : (p12b_V V v).Finite := (p12b_card hcl hv).1
  have hιV : ivsRhoNode1 FF v ∈ V := LOCAL_FAN_IVS_IN_V h2 hv
  have hιV' : ivsRhoNode1 FF v ∈ p12b_V V v := ⟨hιV, IVS_RHO_NODE_DIFF_ID h2 hv⟩
  have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
  have hlf' : LocalFan (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) :=
    p12p_LocalFan hcl hedge hg hv hpi hcard hw0 hcard3
  have hedge' : ∀ x ∈ p12b_V V v, ∃ y, {x, y} ∈ p12b_E V FF v :=
    fun x hx => ⟨p12b_R FF v x, x, hx, rfl⟩
  rw [FAN_PERIMETER hcl.1 hedge, FAN_PERIMETER hlf' hedge']
  rw [show setSum (p12b_V V v) (fun w => arcV 0 w (rhoNode1 (p12b_FF V FF v) w))
      = setSum (p12b_V V v) (fun w => arcV 0 w (p12b_R FF v w)) from
    p13d_setSum_congr (fun w hw => by rw [p12b_rho_FF hw])]
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

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p13c_R_eq_rho_of_ne
#print axioms Kepler.Text.p13d_fanPerimeter

end Kepler.Text

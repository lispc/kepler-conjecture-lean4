/-
Kepler/Text/LocalFanStepBW2.lean — wave C-W2a（D+E+F）：跳跃支的中间角、Σ 坍缩、F 分支。

## 接口修正（相对 WAVE_C_STEPB_PLAN.md 的 W2 原设想）

D（中间点 `interior = π`）在 HOL 的证明锚是 `NKEZBFC.hl:1877-1953`：先证
`∃ i < k-1, bta i = 0 ∧ bta(i+1) = bta(k-1)`（"跳跃索引"），再用 EGHNAVX 的
两条 flat-run 合取得到 `j ≠ 0,i,i+1` 的 `interior(vv j) = π`。**该索引不是 W1
`pW1_gap_setup` 的缺口索引**（后者满足 `0 < bta i < bta(k-1)`，flat-run 前件为假）。
因此本件把 D/E/F 写成**跳跃索引**版本；W7 的 `B` 支（全 0/全 last）会先证跳跃索引
存在（W2b 或 W7），再实例化本件。¬B 缺口支不使用 D（它走 C + W3–W6 的弦矛盾）。

## 件

1. `pW2_interior_eq_pi`（D）：跳跃索引 `bta i = 0`、`bta(i+1) = last` ⇒
   `j ≠ 0,i,i+1` 的 `interiorAngle1 (vv j) = π`。
2. `pW2_sum_collapse`（E）：由 D 得 `setSum V (interior − π) = setSum {v, vv i, vv(i+1)} (…)`。
3. `pW2_some_ge_pi_nonneg`（F）：若 `s` 中某点 `π ≤ interior`，则 `0 ≤ solLocal_p9`。

不含：跳跃索引存在性（B 支，W2b/W7）、k=3、¬B 缺口支几何（W3–W6）。
-/
import Kepler.Text.LocalFanStepBW1

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **D**：跳跃索引两侧的其它点内角 = π（HOL NKEZBFC.hl:1916-1953）。 -/
theorem pW2_interior_eq_pi
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k i : ℕ}
    (hk : V.ncard = k) (hk4 : 3 < k) (hi : i < k - 1) (hi0 : 0 < i)
    (hcol : ∀ w ∈ V, w ≠ v → ¬ Collinear ℝ ({0, v, w} : Set V3))
    (hiter : ∀ j, (rhoNode1_p2 FF)^[j] v = vv j)
    (hbta : ∀ j, azim 0 v (vv 1) (vv j) = bta j)
    (h0 : bta i = 0) (hlast : bta (i + 1) = bta (k - 1)) :
    ∀ j, 0 < j → j < k → j ≠ i → j ≠ i + 1 →
      interiorAngle1_p2 0 FF (vv j) = Real.pi := by
  have hegh := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hv hk hcol hiter hbta
  obtain ⟨-, -, -, hflat⟩ := hegh
  intro j hj0 hjk hji hjis
  rcases lt_or_gt_of_ne hji with hlt | hgt
  · have hc := (hflat i).1 ⟨h0, by omega⟩
    exact hc.1 j ⟨hj0, hlt⟩
  · have hj1 : i + 1 < j := by omega
    by_cases hik : i + 1 = k - 1
    · omega
    · have hlt2 : i + 1 < k - 1 := by omega
      have hpos : 0 < i + 1 := by omega
      have hc := (hflat (i + 1)).2 ⟨hlast, hpos, hlt2⟩
      exact hc.1 j ⟨hj1, hjk⟩

/-- 单点插入的和分解（本地副本，同 TameLp.setSum_insert）。 -/
private theorem pW2_setSum_insert {s : Set V3} {a : V3} (ha : a ∉ s) (hs : s.Finite)
    (f : V3 → ℝ) : setSum (insert a s) f = f a + setSum s f := by
  rw [setSum, setSum, dif_pos (hs.insert a), dif_pos hs,
    Set.Finite.toFinset_insert (hs.insert a)]
  exact Finset.sum_insert (by simpa using ha)

/-- `setSum` 在“子集外为零”时坍缩到子集。 -/
private theorem pW2_setSum_eq_of_zero_off {t : Set V3} (ht : t.Finite) {s : Set V3}
    (hst : s ⊆ t) {f : V3 → ℝ} (hzero : ∀ x ∈ t, x ∉ s → f x = 0) :
    setSum t f = setSum s f := by
  have hs : s.Finite := ht.subset hst
  rw [setSum, setSum, dif_pos ht, dif_pos hs]
  have hsum : (∑ x ∈ hs.toFinset, f x) = ∑ x ∈ ht.toFinset, f x :=
    Finset.sum_subset
      (fun x hx => (Set.Finite.mem_toFinset ht).mpr
        (hst ((Set.Finite.mem_toFinset hs).mp hx)))
      (fun x hxt hxs => hzero x ((Set.Finite.mem_toFinset ht).mp hxt)
        (fun h => hxs ((Set.Finite.mem_toFinset hs).mpr h)))
  exact hsum.symm

/-- **E**：Σ 坍缩到三点集 `{v, vv i, vv (i+1)}`（由 D）。 -/
theorem pW2_sum_collapse
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {k i : ℕ} (hk : V.ncard = k)
    (hiter : ∀ j, (rhoNode1_p2 FF)^[j] v = vv j)
    (hD : ∀ j, 0 < j → j < k → j ≠ i → j ≠ i + 1 →
      interiorAngle1_p2 0 FF (vv j) = Real.pi) :
    setSum V (fun x => interiorAngle1_p2 0 FF x - Real.pi)
      = setSum ({v, vv i, vv (i + 1)} : Set V3)
          (fun x => interiorAngle1_p2 0 FF x - Real.pi) := by
  have h : localFan_p2 V E FF := hcl.1
  have hVfin : V.Finite := LOCAL_FAN_FINITE_V h
  have hsV : ({v, vv i, vv (i + 1)} : Set V3) ⊆ V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hv
    · rw [← hiter i]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i
    · rw [← hiter (i + 1)]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (i + 1)
  refine pW2_setSum_eq_of_zero_off hVfin hsV ?_
  intro x hxV hxs
  have hxmem : x ∈ {(rhoNode1_p2 FF)^[n] v | n < V.ncard} := by
    rw [LOFA_IMP_LT_CARD_SET_V h hv]; exact hxV
  obtain ⟨j, hjk, hxj⟩ := hxmem
  have hxj' : vv j = x := by rw [← hiter j, hxj]
  have hv0 : vv 0 = v := by rw [← hiter 0]; simp
  have hj0 : j ≠ 0 := by
    intro h0
    exact hxs (by rw [← hxj', h0, hv0]; simp)
  have hji : j ≠ i := by
    intro hi
    exact hxs (by rw [← hxj', hi]; simp)
  have hjis : j ≠ i + 1 := by
    intro hi
    exact hxs (by rw [← hxj', hi]; simp)
  have hπ : interiorAngle1_p2 0 FF x = Real.pi := by
    rw [← hxj']
    exact hD j (by omega) (by rw [← hk]; exact hjk) hji hjis
  rw [hπ, sub_self]

/-- `setSum` 的下界：有限集 `s`（`ncard ≤ 3`）上每项 `≥ -π` 且有一项 `≥ 0`，
则 `setSum ≥ -2π`。 -/
private theorem pW2_setSum_lower_bound {s : Set V3} (hs : s.Finite) (hcard : s.ncard ≤ 3)
    {f : V3 → ℝ} (hbot : ∀ x ∈ s, -Real.pi ≤ f x) (hge : ∃ x ∈ s, 0 ≤ f x) :
    -2 * Real.pi ≤ setSum s f := by
  obtain ⟨x0, hx0, hx0ge⟩ := hge
  have hdiff : (s \ {x0}).Finite := hs.sdiff
  have hins : insert x0 (s \ {x0}) = s := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hz, -⟩)
      · exact hx0
      · exact hz
    · intro hz
      by_cases hz0 : z = x0
      · exact Or.inl hz0
      · exact Or.inr ⟨hz, hz0⟩
  have hx0not : x0 ∉ (s \ {x0}) := by
    rw [Set.mem_sdiff]
    simp
  have hdecomp : setSum s f = f x0 + setSum (s \ {x0}) f := by
    conv_lhs => rw [← hins]
    exact pW2_setSum_insert (s := s \ {x0}) (a := x0) hx0not hdiff f
  have hcard' : (s \ {x0}).ncard ≤ 2 := by
    have h := Set.ncard_insert_of_notMem (s := s \ {x0}) (a := x0) hx0not hdiff
    rw [hins] at h
    omega
  have hlow : -Real.pi * ((s \ {x0}).ncard : ℝ) ≤ setSum (s \ {x0}) f := by
    have h := Finset.sum_le_sum (s := hdiff.toFinset) (f := fun _ => -Real.pi) (g := f)
      (fun x hx => hbot x ((Set.Finite.mem_toFinset hdiff).mp hx).1)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    rw [setSum, dif_pos hdiff]
    have hcardeq : ((hdiff.toFinset.card : ℕ) : ℝ) = ((s \ {x0}).ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hdiff]
    rw [← hcardeq]
    simpa [mul_comm] using h
  have hcardR : -Real.pi * ((s \ {x0}).ncard : ℝ) ≥ -2 * Real.pi := by
    have hle : ((s \ {x0}).ncard : ℝ) ≤ 2 := by exact_mod_cast hcard'
    nlinarith [Real.pi_pos]
  linarith

/-- **F**：若三点集中某点 `π ≤ interior`，则 `solLocal_p9 ≥ 0`（HOL NKEZBFC.hl:2039-2048）。 -/
theorem pW2_some_ge_pi_nonneg
    (hcl : convexLocalFan_p2 V E FF) {v u w : V3}
    (hsV : ({v, u, w} : Set V3) ⊆ V)
    (hcollapse : setSum V (fun x => interiorAngle1_p2 0 FF x - Real.pi)
      = setSum ({v, u, w} : Set V3) (fun x => interiorAngle1_p2 0 FF x - Real.pi))
    (hge : ∃ x ∈ ({v, u, w} : Set V3), Real.pi ≤ interiorAngle1_p2 0 FF x) :
    0 ≤ solLocal_p9 E FF := by
  rw [SOL_LOFA_EQ_SUM_INANGLE_p9 hcl, hcollapse]
  have hfin : ({v, u, w} : Set V3).Finite := by
    exact (Set.finite_singleton w).insert u |>.insert v
  have hcard : ({v, u, w} : Set V3).ncard ≤ 3 := by
    have h := Set.ncard_insert_le (v) ({u, w} : Set V3)
    have h2 := Set.ncard_insert_le (u) ({w} : Set V3)
    simp only [Set.ncard_singleton] at h2
    omega
  have hbot : ∀ x ∈ ({v, u, w} : Set V3), -Real.pi ≤ interiorAngle1_p2 0 FF x - Real.pi := by
    intro x hx
    have hxV : x ∈ V := hsV hx
    have hpos := INTERIOR_ANGLE1_POS hcl.1 hxV
    linarith
  have hge' : ∃ x ∈ ({v, u, w} : Set V3), 0 ≤ interiorAngle1_p2 0 FF x - Real.pi := by
    obtain ⟨x, hx, hxge⟩ := hge
    exact ⟨x, hx, by linarith⟩
  have h := pW2_setSum_lower_bound hfin hcard hbot hge'
  linarith [Real.pi_pos]

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW2_interior_eq_pi
#print axioms Kepler.Text.pW2_sum_collapse
#print axioms Kepler.Text.pW2_some_ge_pi_nonneg

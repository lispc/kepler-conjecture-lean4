/-
Kepler/Text/LocalFanStepW5B.lean — wave C-W5b（w 侧 2406-2498，第一件）：w 侧 flat-run 成员。

件目（W5b-i，本件）：
* `pW5b_flat_mem`：w 侧 flat-run 的逐点成员——
  `i+1 ≤ n → n < k → vv n ∈ affGt {0,v}{ιv}`。
  路线：`EGHNAVX` 第二条件式合取（前件 `bta(i+1) = last ∧ 0<i+1 ∧ i+1<k-1`，
  集合包含 `{vv n | i+1 ≤ n < k} ⊆ affGt{0,v}{ιv}`）；边界 `i+1 = k-1`
  时唯一元素是 `vv(k-1) = ιv`，用 `affGt_pair_iff` 的自成员性（c=1,h=0）。

依赖：本件**不吃 `hprev`**（只用 EGHNAVX 第二合取 + 周期/反向件）。
后续 W5b-ii（w 侧 dart 级包含）吃 `pW5w_telescope`（`hprev` 显式槽）与
`pW4b_iter_ee_mem`。
-/
import Kepler.Text.LocalFanStepW5W
import Kepler.Text.LocalFanStepBW4

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **w 侧 flat-run 逐点成员**：`i+1 ≤ n < k` ⇒ `vv n ∈ affGt{0,v}{ιv}`。 -/
theorem pW5b_flat_mem
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k - 1) (hbi : bta (i + 1) = bta (k - 1))
    {n : ℕ} (hn1 : i + 1 ≤ n) (hnk : n < k) :
    vv n ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v} := by
  have hl : localFan_p2 V E FF := hcl.1
  have hcol : ∀ w ∈ V, w ≠ v → ¬ Collinear ℝ ({0, v, w} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hl (fun _ _ => trivial) hg v hv
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ m, vv m ∈ V := by
    intro m
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hl hv m
  have hvk1 : vv (k - 1) = ivsRhoNode1_p2 FF v := by
    rw [← hiter (k - 1), show k - 1 = V.ncard - 1 from by omega]
    exact ITER_CARD_MINUS1_EQ_IVS_RN1 hl hv
  by_cases hedge : i + 1 < k - 1
  · -- EGHNAVX 第二合取
    have hegh := EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hv hk hcol hiter hbta
    obtain ⟨-, -, -, hD⟩ := hegh
    have hsub := ((hD (i + 1)).2 ⟨hbi, by omega, hedge⟩).2
    rw [hvk1] at hsub
    exact hsub ⟨n, hn1, hnk, rfl⟩
  · -- 边界：i+1 = k-1，唯一 n = k-1，直接自成员
    have hnk' : n = k - 1 := by omega
    rw [hnk', hvk1]
    have h0v : (0 : V3) ≠ v := fun h => h0V (h ▸ hv)
    have hιV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hl hv
    have hι0 : ivsRhoNode1_p2 FF v ≠ 0 := fun h => h0V (h ▸ hιV)
    have hιv : ivsRhoNode1_p2 FF v ≠ v := by
      intro h
      exact (LOFA_IMP_NOT_COLL_IVS hl hv) (by
        rw [h]; exact collinear3_pair_right rfl)
    refine (affGt_pair_iff (v0 := (0 : V3)) (v1 := v)
      (x := ivsRhoNode1_p2 FF v) (y := ivsRhoNode1_p2 FF v)
      h0v hι0 hιv).mpr ⟨1, one_pos, 0, ?_⟩
    rw [one_smul, zero_smul, add_zero]

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5b_flat_mem
#print axioms Kepler.Text.pW5b_flat_mem

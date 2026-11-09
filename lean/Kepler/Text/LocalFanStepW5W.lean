/-
Kepler/Text/LocalFanStepW5W.lean — wave C-W5a（w 侧镜像 telescope）。

HOL 锚：`NKEZBFC.hl:2346`：
  `∀ j < k-i-1, affGe {0}{v, vv(k-j-1)} = ⋃_{j1≤j} affGe {0}{vv(k-j1-1), vv(k-j1)}`

件目（本波 W5a-i）：
* §1 `pW5w_telescope`（telescope 本体，~70 行）：对 j 归纳；步进
  `AFF_GE_EQ_AFF_GE_UNION_p9`（x=0, v=v, u=vv(k-j-2), v1=vv(k-j-1)），
  其 `h4 : vv(k-j-1) ∈ affGt {0}{v, vv(k-j-2)}` 作为**显式滑动前提**
  `hprev : ∀ n, i+1 ≤ n → n ≤ k-1 → vv n ∈ affGt {0}{v, vv(n-1)}` 接收。
* §2 `pW5w_base`（基例，~12 行）：`vv k = v` 直接吃
  `LOFA_IMP_ITER_RHO_NODE_ID`（LA5:7706），**不重造**；基例 = 集合换序。
* §3 `pW5w_telescope_k`（接线，~10 行）：把 §1/§2 组成对
  `k = V.ncard` 的最终形。

**重要接口发现**：w 侧步进的 `h4` 是**反向锥形**
`vv n ∈ affGt {0}{v, vv(n-1)}`（previous-point），**不是**
`pW5_flat_cone_order` 的正向形 `vv n ∈ affGt{0}{v,vv(n+1)}` 的逐字镜像；
后者按 `m := k-1-n` 换序才同形（见 DELIVERY §3）。其推导留 W5a-ii。
-/
import Kepler.Text.LocalFanStepBW3c
import Kepler.Text.LocalFanStepW5ConeB

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 w 侧 telescope 本体 -/

/-- **w 侧 telescope（条件形）**：`hprev` 显式接收反向锥形步进前提。 -/
theorem pW5w_telescope
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {i : ℕ}
    (hprev : ∀ n, i + 1 ≤ n → n ≤ V.ncard - 1 →
      vv n ∈ affGt ({0} : Set V3) {v, vv (n - 1)}) :
    ∀ j, j < V.ncard - i - 1 → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {v, vv (V.ncard - j - 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3)
            {vv (V.ncard - j1 - 1), vv (V.ncard - j1)} := by
  have hvk : vv V.ncard = v := by
    rw [← hiter V.ncard]
    exact LOFA_IMP_ITER_RHO_NODE_ID hcl.1 hv
  have hvv0 : vv 0 = v := by
    rw [← hiter 0]
    simp
  have hVV : ∀ n, vv n ∈ V := by
    intro n
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv n
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hdisj : ∀ a b : ℕ, Disjoint ({0} : Set V3) {vv a, vv b} := by
    intro a b
    refine Set.disjoint_singleton_left.mpr ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h0V (h ▸ hVV a), fun h => h0V (h ▸ hVV b)⟩
  intro j
  induction j with
  | zero =>
      intro _ z
      constructor
      · intro hz
        refine ⟨0, le_refl 0, ?_⟩
        have h1 : vv (V.ncard - 0) = v := by
          rw [show V.ncard - 0 = V.ncard from by omega, hvk]
        rw [h1, show V.ncard - 0 - 1 = V.ncard - 1 from by omega]
        rwa [show ({vv (V.ncard - 1), v} : Set V3)
          = {v, vv (V.ncard - 1)} from Set.pair_comm _ _]
      · rintro ⟨j1, hj1, hz⟩
        have hj1' : j1 = 0 := by omega
        rw [hj1'] at hz
        rw [show V.ncard - 0 - 1 = V.ncard - 1 from by omega,
          show V.ncard - 0 = V.ncard from by omega, hvk,
          show ({vv (V.ncard - 1), v} : Set V3)
            = {v, vv (V.ncard - 1)} from Set.pair_comm _ _] at hz
        rw [show V.ncard - 0 - 1 = V.ncard - 1 from by omega]
        exact hz
  | succ j ih =>
      intro hj z
      have hj' : j < V.ncard - i - 1 := by omega
      have hIH := ih hj'
      have hidx : V.ncard - (j + 1) - 1 = V.ncard - j - 1 - 1 := by omega
      have hidx2 : V.ncard - (j + 1) = V.ncard - j - 1 := by omega
      have hst : vv (V.ncard - j - 1) ∈ affGt ({0} : Set V3)
          {v, vv (V.ncard - j - 1 - 1)} :=
        hprev (V.ncard - j - 1) (by omega) (by omega)
      have hEq := AFF_GE_EQ_AFF_GE_UNION_p9 (x := (0 : V3)) (v := v)
        (u := vv (V.ncard - j - 1 - 1)) (v1 := vv (V.ncard - j - 1))
        (by rw [← hvv0]; exact hdisj 0 (V.ncard - j - 1 - 1)) (by rw [← hvv0]; exact hdisj 0 (V.ncard - j - 1))
        (hdisj (V.ncard - j - 1) (V.ncard - j - 1 - 1)) hst
      rw [hidx, hEq, Set.mem_union]
      constructor
      · rintro (hz | hz)
        · obtain ⟨j1, hj1, hz'⟩ := (hIH z).mp hz
          exact ⟨j1, by omega, hz'⟩
        · refine ⟨j + 1, le_refl _, ?_⟩
          rw [hidx, hidx2]
          rwa [show ({vv (V.ncard - j - 1 - 1), vv (V.ncard - j - 1)} : Set V3)
            = {vv (V.ncard - j - 1), vv (V.ncard - j - 1 - 1)} from Set.pair_comm _ _]
      · rintro ⟨j1, hj1, hz⟩
        rcases Nat.lt_or_ge j1 (j + 1) with hlt | hge
        · exact Or.inl ((hIH z).mpr ⟨j1, by omega, hz⟩)
        · right
          have hje : j1 = j + 1 := by omega
          rw [show ({vv (V.ncard - j - 1), vv (V.ncard - j - 1 - 1)} : Set V3)
            = {vv (V.ncard - j - 1 - 1), vv (V.ncard - j - 1)} from Set.pair_comm _ _]
          simpa [hje, hidx, hidx2] using hz

/-! ## §2 基例（周期件：LA5:7706） -/

/-- **基例**：`vv k = v`（`LOFA_IMP_ITER_RHO_NODE_ID`），基例恒等式成立。 -/
theorem pW5w_base (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n) (z : V3) :
    z ∈ affGe ({0} : Set V3) {v, vv (V.ncard - 1)}
      ↔ z ∈ affGe ({0} : Set V3) {vv (V.ncard - 1), v} := by
  have hvk : vv V.ncard = v := by
    rw [← hiter V.ncard]
    exact LOFA_IMP_ITER_RHO_NODE_ID hcl.1 hv
  rw [Set.pair_comm (vv (V.ncard - 1)) v]

/-! ## §3 最终接线 -/

/-- **`pW5w_telescope_final`**：`k = V.ncard` 的直接形（等同 §1 的零索引展开）。 -/
theorem pW5w_telescope_final
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {i : ℕ}
    (hprev : ∀ n, i + 1 ≤ n → n ≤ V.ncard - 1 →
      vv n ∈ affGt ({0} : Set V3) {v, vv (n - 1)}) :
    ∀ j, j < V.ncard - i - 1 → ∀ z : V3,
      z ∈ affGe ({0} : Set V3) {v, vv (V.ncard - j - 1)}
        ↔ ∃ j1, j1 ≤ j ∧ z ∈ affGe ({0} : Set V3)
            {vv (V.ncard - j1 - 1), vv (V.ncard - j1)} :=
  pW5w_telescope hcl hv hiter hprev

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w_telescope
#print axioms Kepler.Text.pW5w_telescope
#check @Kepler.Text.pW5w_base
#print axioms Kepler.Text.pW5w_base
#check @Kepler.Text.pW5w_telescope_final
#print axioms Kepler.Text.pW5w_telescope_final

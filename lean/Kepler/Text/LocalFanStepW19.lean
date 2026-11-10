/-
Kepler/Text/LocalFanStepW19.lean — wave W19：stepB 槽装配（下游同形重述）。

结构（LA9 零编辑；`NKEZBFC_PREP_p9`（LA9:3196，证明体为占位桩）→ 下游同形重述，
先例 `EJRCFJD_ALT2`）：

* §1 `pW19_mem_affGe_pair_left/right`：对顶点自成员
  （`x ∈ affGe {0}{x,y}`、`y ∈ affGe {0}{x,y}`；`Affsign.of_triple` 系数 1/0）。
* §2 `pW19_stepB_sol_nonneg`：装配——
  真支（`3 < V.ncard`）：`pW6k8_stepB_sol_nonneg_affGe` 的两 affGe 槽由望远镜直供：
  u 侧 = `pW4_telescope_u`（前向 `hstep` 槽，端点自成员）；
  w 侧 = `pW5w_telescope`（后向 `hprev` 槽，i := 0，端点自成员 + Nat.sub 索引配平）；
  假支：`CARD_VERTEX_GE_3_LOCAL_FAN_p9` ⇒ ncard = 3 ⇒ `SOL_LOCAL_FAN_POS_CASE3_p9`。
  **两槽为诚实显式前提**（W5W 望远镜终点几何，未消）。
* §3 `pW19_nkezbfc_prep_p9`：LA9:3196 陈述逐字 + 几何槽前提的下游重述
  := `p9_main_induction h pW19_stepB_slot-form V.ncard V E FF hcl hg rfl`。
-/
import Kepler.Text.LocalAuto9
import Kepler.Text.LocalFanStepW6K8

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 对顶点自成员 -/

/-- `x ∈ affGe {0} {x, y}`。 -/
theorem pW19_mem_affGe_pair_left {x y : V3} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    x ∈ affGe ({0} : Set V3) {x, y} :=
  Affsign.of_triple (sgn := fun r => 0 ≤ r) (x := (0 : V3)) (v := x) (u := y)
    (y := x) 1 0 (by norm_num) (by norm_num) (by module) (Ne.symm hx0)
    (Ne.symm hy0) hxy

/-- `y ∈ affGe {0} {x, y}`。 -/
theorem pW19_mem_affGe_pair_right {x y : V3} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    y ∈ affGe ({0} : Set V3) {x, y} :=
  Affsign.of_triple (sgn := fun r => 0 ≤ r) (x := (0 : V3)) (v := x) (u := y)
    (y := y) 0 1 (by norm_num) (by norm_num) (by module) (Ne.symm hx0)
    (Ne.symm hy0) hxy

/-! ## ## §2 stepB 槽装配（hstep/hprev 望远镜几何槽显式保留） -/

/-- **W19 装配**：stepB 形（`hstep` 前向 / `hprev` 后向两个望远镜几何槽显式保留）。 -/
theorem pW19_stepB_sol_nonneg
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
    (hprev : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 1 ≤ n → n ≤ V.ncard - 1 →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  by_cases hlt : 3 < V.ncard
  · refine pW6k8_stepB_sol_nonneg_affGe hcl hg hnc hlt ?_ ?_
    · -- u 侧 affGe 槽：pW4_telescope_u + 端点自成员
      intro p hp j hj0 hj
      have hstepb : ∀ n : ℕ, 0 < n → n + 1 ≤ j →
          (rhoNode1_p2 FF)^[n] p ∈ affGt ({0} : Set V3)
            {p, (rhoNode1_p2 FF)^[n + 1] p} :=
        fun n hn hnj => hstep p hp (fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl)
          n hn (by omega)
      have htel := pW4_telescope_u (i := j) hcl hp
        (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hstepb
      have hne1 : (rhoNode1_p2 FF)^[j - 1] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[j - 1] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp (j - 1)
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne2 : (rhoNode1_p2 FF)^[j] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[j] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp j
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne12 : (rhoNode1_p2 FF)^[j - 1] p ≠ (rhoNode1_p2 FF)^[j] p := by
        have hd := LOFA_IMP_DIS_ELMS23 hlf hp (j - 1) j (by omega) (by omega)
        exact Ne.symm hd
      have hidxj : j - 1 + 1 = j := by omega
      have hmemL : (rhoNode1_p2 FF)^[j - 1] p ∈ affGe ({0} : Set V3)
          {(rhoNode1_p2 FF)^[j - 1] p, (rhoNode1_p2 FF)^[j - 1 + 1] p} := by
        rw [hidxj]
        exact pW19_mem_affGe_pair_left hne1 hne2 hne12
      have hz := (htel (j - 1) (by omega) ((rhoNode1_p2 FF)^[j - 1] p)).mpr
        ⟨j - 1, le_rfl, hmemL⟩
      rw [hidxj] at hz
      have hιeq : ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)
          = (rhoNode1_p2 FF)^[j - 1] p :=
        pW6k6_iter_ivs hlf hp (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hj0
      rw [hιeq]
      exact hz
    · -- w 侧 affGe 槽：pW5w_telescope（i := 0）+ 端点自成员
      intro p hp j hj
      have hprevb : ∀ n : ℕ, 0 + 1 ≤ n → n ≤ V.ncard - 1 →
          (rhoNode1_p2 FF)^[n] p ∈ affGt ({0} : Set V3)
            {p, (rhoNode1_p2 FF)^[n - 1] p} :=
        fun n hn hk => hprev p hp (fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl)
          n (by omega) hk
      have htel := pW5w_telescope (i := 0) hcl hp
        (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hprevb
      have hjt : V.ncard - j - 2 < V.ncard - 0 - 1 := by omega
      have hne1 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne2 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ≠ 0 := by
        intro hcon
        have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ∈ V :=
          LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
        exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
      have hne12 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p
          ≠ (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p := by
        have hd := LOFA_IMP_DIS_ELMS23 hlf hp
          (V.ncard - (V.ncard - j - 2) - 1) (V.ncard - (V.ncard - j - 2))
          (by omega) (by omega)
        exact Ne.symm hd
      have hidx1 : V.ncard - (V.ncard - j - 2) - 1 = j + 1 := by omega
      have hidx2 : V.ncard - (V.ncard - j - 2) = j + 2 := by omega
      have hz := (htel (V.ncard - j - 2) hjt
        ((rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p)).mpr
        ⟨V.ncard - j - 2, le_rfl,
          pW19_mem_affGe_pair_right hne1 hne2 hne12⟩
      rw [hidx1] at hz
      rw [hidx2] at hz
      have hρw : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j + 1] p) = (rhoNode1_p2 FF)^[j + 2] p := by
        rw [show j + 2 = Nat.succ (j + 1) from rfl]
        exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (j + 1) p).symm
      rw [hρw]
      exact hz
  · -- 假支：ncard = 3
    have h3 : 3 ≤ V.ncard := CARD_VERTEX_GE_3_LOCAL_FAN_p9 hcl
    exact SOL_LOCAL_FAN_POS_CASE3_p9 hcl (by omega)

/-! ## ## §3 LA9:3196 下游同形重述 -/

/-- `NKEZBFC_PREP_p9`（LA9:3196，证明体占位桩）的下游同形重述：陈述逐字 + 几何槽前提。 -/
theorem pW19_nkezbfc_prep_p9
    (h : EJRCFJD_concl_p9)
    (hslots : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
      ∧ (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 1 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})) :
    ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E → 0 ≤ solLocal_p9 E FF := by
  intro V E FF hcl hg
  exact p9_main_induction h
    (fun V' E' FF' hcl' hg' hnc' =>
      pW19_stepB_sol_nonneg hcl' hg' hnc'
        (hslots V' E' FF' hcl' hg').1 (hslots V' E' FF' hcl' hg').2)
    V.ncard V E FF hcl hg rfl

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW19_stepB_sol_nonneg
#print axioms Kepler.Text.pW19_mem_affGe_pair_left
#print axioms Kepler.Text.pW19_stepB_sol_nonneg
#print axioms Kepler.Text.pW19_nkezbfc_prep_p9

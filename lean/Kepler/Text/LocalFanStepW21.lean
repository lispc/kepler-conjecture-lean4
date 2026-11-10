/-
Kepler/Text/LocalFanStepW21.lean — wave W21 patch ①：槽范围更正 v2（两转换件 + j=0 反证）。

范围侦察（机器事实）：
* `pW5w_telescope` 的 `hprev` 消费点在 `n = k−j−1`（induction step），
  `i := 1` 时覆盖 `n ∈ [3, k−1]` ⊂ `[2, k−1]` ⇒ **hprev v2（n ≥ 2）够用**，
  结论界 `j' < k−2` ⇒ 槽索引 `j ≥ 1`。
* **第二处假支（新发现）**：`hslot_w` 的 `j = 0` 实例要求
  `ρ(vv 1) = vv 2 ∈ affGe {0}{p, vv 1}`——但 `vv 2` 一般不在
  `cone{p, vv 1}`（射线序外）⇒ 该实例与 `azim 0 p (vv 1) (vv 2) ≠ 0`
  矛盾（§3 形式反证）。⇒ **v2 槽的诚实范围为 `j ≥ 1`**（与 `hslot_u`
  的 `0 < j` 一致；两槽的消费者 `pW6k7` K 案只在 `j := i₀ ≥ 1` 处消费）。

件目：
* §1 `pW21_slot_u_v2`：u 槽 affGe 成员由 hstep（前向）直供（j ≥ 1）。
* §2 `pW21_slot_w_v2`：w 槽 affGe 成员由 hprev-v2（n ≥ 2，telescope i := 1）直供（j ≥ 1）。
* （`j = 0` 实例的形式反证 `pW21_wslot_zero_false` 留 W22：需 cone 坐标
  extractor + azim 退化排除，本轮预算外；判定见 DELIVERY。）
-/
import Kepler.Text.LocalFanStepW20
import Kepler.Text.LocalFanStepW5ConeB

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 u 槽 v2 转换（hstep 前向，j ≥ 1） -/

/-- **u 槽 v2**：`hstep`（前向，全 n 形）⇒ `ι(vv j) ∈ affGe {0}{p, vv j}`（j ≥ 1）。 -/
theorem pW21_slot_u_v2 (hcl : convexLocalFan_p2 V E FF) {p : V3} (hp : p ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    {j : ℕ} (hj0 : 0 < j) (hj : j + 1 < V.ncard)
    (hstep : ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
      vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)}) :
    ivsRhoNode1_p2 FF (vv j) ∈ affGe ({0} : Set V3) {p, vv j} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ n, vv n ∈ V := fun n => by
    rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  have hstepb : ∀ n : ℕ, 0 < n → n + 1 ≤ j →
      vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)} :=
    fun n hn hnj => hstep n hn (by omega)
  have htel := pW4_telescope_u (i := j) hcl hp hiter hstepb
  have hne1 : vv (j - 1) ≠ 0 := fun hcon => h0V (hcon ▸ hVV (j - 1))
  have hne2 : vv j ≠ 0 := fun hcon => h0V (hcon ▸ hVV j)
  have hne12 : vv (j - 1) ≠ vv j := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp (j - 1) j (by omega) (by omega)
    rw [hiter j, hiter (j - 1)] at hd
    exact Ne.symm hd
  have hidxj : j - 1 + 1 = j := by omega
  have hmemL : vv (j - 1) ∈ affGe ({0} : Set V3) {vv (j - 1), vv (j - 1 + 1)} := by
    rw [hidxj]
    exact pW19_mem_affGe_pair_left hne1 hne2 hne12
  have hz := (htel (j - 1) (by omega) (vv (j - 1))).mpr ⟨j - 1, le_rfl, hmemL⟩
  rw [hidxj] at hz
  have hιeq : ivsRhoNode1_p2 FF (vv j) = vv (j - 1) :=
    pW6k6_iter_ivs hlf hp hiter hj0
  rw [hιeq]
  exact hz

/-! ## §2 w 槽 v2 转换（hprev-v2 n ≥ 2，telescope i := 1，j ≥ 1） -/

/-- **w 槽 v2**：`hprev`（n ≥ 2 诚实范围）⇒ `ρ(vv(j+1)) ∈ affGe {0}{p, vv(j+1)}`（j ≥ 1）。 -/
theorem pW21_slot_w_v2 (hcl : convexLocalFan_p2 V E FF) {p : V3} (hp : p ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    {j : ℕ} (hj0 : 0 < j) (hj : j + 2 < V.ncard)
    (hprev : ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
      vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) :
    rhoNode1_p2 FF (vv (j + 1)) ∈ affGe ({0} : Set V3) {p, vv (j + 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ n, vv n ∈ V := fun n => by
    rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  have hprevb : ∀ n : ℕ, 1 + 1 ≤ n → n ≤ V.ncard - 1 →
      vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)} :=
    fun n hn hk => hprev n (by omega) hk
  have htel := pW5w_telescope (i := 1) hcl hp hiter hprevb
  have hjt : V.ncard - j - 2 < V.ncard - 1 - 1 := by omega
  have hne1 : vv (V.ncard - (V.ncard - j - 2) - 1) ≠ 0 :=
    fun hcon => h0V (hcon ▸ hVV _)
  have hne2 : vv (V.ncard - (V.ncard - j - 2)) ≠ 0 :=
    fun hcon => h0V (hcon ▸ hVV _)
  have hne12 : vv (V.ncard - (V.ncard - j - 2) - 1)
      ≠ vv (V.ncard - (V.ncard - j - 2)) := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp
      (V.ncard - (V.ncard - j - 2) - 1) (V.ncard - (V.ncard - j - 2))
      (by omega) (by omega)
    rw [hiter (V.ncard - (V.ncard - j - 2)),
      hiter (V.ncard - (V.ncard - j - 2) - 1)] at hd
    exact Ne.symm hd
  have hidx1 : V.ncard - (V.ncard - j - 2) - 1 = j + 1 := by omega
  have hidx2 : V.ncard - (V.ncard - j - 2) = j + 2 := by omega
  have hz := (htel (V.ncard - j - 2) hjt
    (vv (V.ncard - (V.ncard - j - 2)))).mpr
    ⟨V.ncard - j - 2, le_rfl,
      pW19_mem_affGe_pair_right hne1 hne2 hne12⟩
  rw [hidx1] at hz
  rw [hidx2] at hz
  have hρw : rhoNode1_p2 FF (vv (j + 1)) = vv (j + 2) := by
    rw [← hiter (j + 1), ← hiter (j + 2)]
    rw [show j + 2 = Nat.succ (j + 1) from rfl]
    exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (j + 1) p).symm
  rw [hρw]
  exact hz

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW21_slot_u_v2
#print axioms Kepler.Text.pW21_slot_w_v2

/-
Kepler/Text/LocalFanStepW34.lean — wave W34：J 段收尾（HOL NKEZBFC.hl:2499–2583）。

**AZIM_COMPL 族对表（工单要求，先对表后写）**：
* `AZIM_COMPL` ↔ `Kepler.Geom.azim_compl`（AzimLemmas:318，**std3 ✓**；
  语句：`azim z w w2 w1 = if azim z w w1 w2 = 0 then 0 else 2π − azim z w w1 w2`）；
* `azim_compl_eq_zero`（AzimLemmas:407，std3 ✓）；`AZIM_COMPL_EXT`
  （PackingAuto6:3489，std3 ✓）；`AZIM_COMPL_NEG_fb`（FanBaseKit:407，std3 ✓）；
* **缺件/禁用**：`AZIM_COMPL_NEG_p13`（LocalAuto13:1526）与 `AZIM_NEG_p13`
  ——**证体 `sorry`，禁用**；p13 `-v` 变体族整体不可消费。
* `point_in_aff_ge`（Planarity:4334，std3 ✓）= HOL 同名件（三成员合取）。
* `LOCAL_FAN_ORBIT_MAP_VITER` ↔ 树内 `LOCAL_FAN_ORBIT_MAP_VITERFF`
  （LocalAuto35:19109 面轨道 kit；未被本件消费）。

**J 段结构判定（机器证据，对表结论）**：HOL 的 `ρw ∈ aff_ge{0}{v,w}`
（SUBGOAL :2520）证明 = 平凡对成员（`point_in_aff_ge` 给
`ρw ∈ aff_ge{0}{w, ρw}`）+ **w 侧 union 望远镜等式**（H 段 :2345–2400 的
`∀j` 归纳，`AFF_GE_EQ_AFF_GE_UNION` 步进，h4 由 `th3` 供给）。⇒ J 与 H 是
**同一归纳**的两面（h4 的 1_2 步进与 mirror hstep 同源）——详见 DELIVERY
架构发现；本件交付可独立收尾的 **wrap 基点**（`w = vv(k-1)`，`ρw = p`，
无需望远镜）。
-/
import Kepler.Text.LocalFanStepW32

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 J 段 wrap 基点 -/

/-- **J 段收尾（wrap 基点）**：`w = vv(k−1)` 处 `ρw = p`（周期回卷）⇒
`ρw ∈ affGe{0}{p, w}`（p 为生成元，`point_in_aff_ge`/对成员直取）。
= HOL J 段在 `j = 0` 端点的实例（无需 w 侧 union 望远镜）。 -/
theorem pW34_rho_last_mem (hcl : convexLocalFan_p2 V E FF) {p : V3} (hp : p ∈ V)
    {vv : ℕ → V3} {k : ℕ} (hk : V.ncard = k) (hk2 : 1 < k)
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n) :
    rhoNode1_p2 FF (vv (k - 1)) ∈ affGe ({0} : Set V3) {p, vv (k - 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  -- ρ(vv(k-1)) = vv k = p（周期回卷）
  have hρ : rhoNode1_p2 FF (vv (k - 1)) = p := by
    have hstep : rhoNode1_p2 FF (vv (k - 1)) = vv ((k - 1) + 1) := by
      rw [← hiter (k - 1), ← hiter ((k - 1) + 1)]
      rw [Function.iterate_succ_apply']
    rw [hstep, show k - 1 + 1 = k from by omega]
    rw [← hk]
    exact (hiter V.ncard).symm.trans (LOFA_IMP_ITER_RHO_NODE_ID hlf hp)
  rw [hρ]
  -- p 是对成员
  have hp0 : p ≠ (0 : V3) := fun h => h0V (h ▸ hp)
  have hwV : vv (k - 1) ∈ V := by
    rw [← hiter (k - 1)]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp (k - 1)
  have hw0 : vv (k - 1) ≠ (0 : V3) := fun h => h0V (h ▸ hwV)
  have hpw : p ≠ vv (k - 1) := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 (k - 1) (by omega) (by omega)
    rw [hiter (k - 1), show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact fun h => hd h.symm
  exact pW19_mem_affGe_pair_left hp0 hw0 hpw

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW34_rho_last_mem

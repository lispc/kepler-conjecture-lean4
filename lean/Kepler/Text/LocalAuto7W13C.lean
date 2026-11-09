/-
LocalAuto7W13C: W13b — straight 支 `Generic V' E'`（HOL polar_fan.hl:2825-2880）。

`Generic V E`（LA1:117）**不带数据槽**，本体是
`∀ v w u, {v,w} ∈ E → u ∈ V → affGe {0}{v,w} ∩ affLt {0}{u} = ∅`。
straight 支的 `E'` 只有两类边（HOL 2825-2840 的结构事实）：

* **旧边** `{w, ρw} ∈ E`（`r w = ρw`，即 `ρw ≠ v`）；
* **合并边** `{ιv, ρv}`（唯一例外：`ρw = v` 即 `w = ιv` 处 `r` 偏离 `ρ`）。

`p13c_E_subset` 把这条二分落成 `E' ⊆ insert {ιv,ρv} E`。于是 `Generic V' E'` 只剩：
旧边直接继承 `hg`（`u ∈ V' ⊆ V`）；合并边用 `UNION_AFF_GE_1_2` 拆成
`affGe{0}{ιv,v} ∪ affGe{0}{v,ρv}`（`hmem` = `p12b_straight_mem`，三点非零由 `fan2`
即 `0 ∉ V` 供），两块各被 `hg` 在旧边 `{ιv,v}`、`{v,ρv}` 上杀空。

件表：`p13c_E_subset` / `p13c_ivs_v_edge` / `p13c_generic`。
W13A / W13B / W12E–P / LA7 零改动；**无新增 import**。
-/
import Kepler.Text.LocalAuto7W13B

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## `E'` 的边二分（HOL 2825-2840） -/

/-- **`E' ⊆ insert {ιv, ρv} E`**：`E'` 的边只有「旧边 `{w,ρw}`」与「合并边 `{ιv,ρv}`」。
`ρw ≠ v` 时 `r w = ρw`（`LOCAL_RHO_NODE_PAIR_E` 给旧边）；`ρw = v` 时 `w = ιv`
（`IVS_RHO_IDD`），`r w = ρv`（合并边）。 -/
theorem p13c_E_subset {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    p12b_E V FF v ⊆ insert ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3) E := by
  rintro e ⟨w, hw, rfl⟩
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  unfold p12b_R
  by_cases hc : rhoNode1 FF w = v
  · rw [if_pos hc]
    have hwivs : w = ivsRhoNode1 FF v := by
      have hid : ivsRhoNode1 FF (rhoNode1 FF w) = w := IVS_RHO_IDD h2 hw.1
      rw [hc] at hid
      exact hid.symm
    rw [hwivs]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · rw [if_neg hc]
    exact Set.mem_insert_iff.mpr (Or.inr (LOCAL_RHO_NODE_PAIR_E h2 hw.1))

/-- `{ιv, v} ∈ E`（合并边拆分的第一块）：`(ιv, v)` 是 `FF` 的 dart（`ρ(ιv) = v`）。 -/
theorem p13c_ivs_v_edge {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ({ivsRhoNode1 FF v, v} : Set V3) ∈ E := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hιV : ivsRhoNode1 FF v ∈ V := LOCAL_FAN_IVS_IN_V h2 hv
  have h := LOCAL_RHO_NODE_PAIR_E h2 hιV
  rw [show rhoNode1_p2 FF (ivsRhoNode1 FF v) = v from
    LOCAL_FAN_RHO_NODE_IVS h2 hv] at h
  exact h

/-! ## `Generic V' E'`（HOL 2825-2880） -/

/-- **`Generic V' E'`**：旧边继承 `hg`；合并边 `{ιv,ρv}` 经 `UNION_AFF_GE_1_2` 拆成
`affGe{0}{ιv,v}` 与 `affGe{0}{v,ρv}` 两块，各由 `hg` 在 `{ιv,v}` / `{v,ρv}` 上杀空
（`v ∈ affGe{0}{ιv,ρv}` 由 `p12b_straight_mem` 供，三点非零由 `0 ∉ V` 供）。 -/
theorem p13c_generic {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    Generic (p12b_V V v) (p12b_E V FF v) := by
  intro e1 e2 u he hu
  have huV : u ∈ V := hu.1
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  rcases Set.mem_insert_iff.mp (p13c_E_subset hcl hedge he) with hmerged | hold
  · rw [hmerged]
    have h0V : (0:V3) ∉ V := (hcl.1.1).2.2.2.1
    have hιV : ivsRhoNode1 FF v ∈ V := LOCAL_FAN_IVS_IN_V h2 hv
    have hρV : rhoNode1 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h2 hv
    rw [show affGe ({0} : Set V3) ({ivsRhoNode1 FF v, rhoNode1 FF v} : Set V3)
        = affGe {0} {ivsRhoNode1 FF v, v} ∪ affGe {0} {v, rhoNode1 FF v}
        from (UNION_AFF_GE_1_2 0 (ivsRhoNode1 FF v) v (rhoNode1 FF v)
          (p12b_straight_mem hcl hedge hg hv hpi)
          (fun h => h0V (h ▸ hιV)) (fun h => h0V (h ▸ hv))
          (fun h => h0V (h ▸ hρV))).symm]
    rw [Set.union_inter_distrib_right,
      hg (ivsRhoNode1 FF v) v u (p13c_ivs_v_edge hcl hedge hv) huV,
      hg v (rhoNode1 FF v) u (LOCAL_RHO_NODE_PAIR_E h2 hv) huV]
    exact Set.empty_union _
  · exact hg e1 e2 u hold huV

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p13c_E_subset
#print axioms Kepler.Text.p13c_ivs_v_edge
#print axioms Kepler.Text.p13c_generic

end Kepler.Text

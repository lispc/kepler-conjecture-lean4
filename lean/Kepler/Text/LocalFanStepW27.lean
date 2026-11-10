/-
Kepler/Text/LocalFanStepW27.lean — wave W27：`hslot_w` 的 j = 0 假支形式反证 + 诚实域桥。

判定入账（W21 发现、W26 图谱第二格）：`hslot_w` 的 j = 0 实例要求
`ρ(ρ(p)) = vv 2 ∈ affGe {0}{p, ρ(p)}`（即 `vv 2` 在 cone{p, vv 1} 内），
但径向序一般分居（`bta 2 ≠ 0` 时 `vv 2` 严格在锥外）⇒ 该实例与
`azim 0 (vv 1) (vv 2) p ≠ 0` 矛盾（成员判定件
`pW6k6_azim_zero_of_affGe` 的逆否 + `azim_eq_zero_symm`）。

件目：
* §1 `pW27_wslot_zero_false`：j = 0 断言之否定（`¬(vv 2 ∈ cone{p, vv 1})`
  的可实例化反例形式；非共线前提 + 径向非零前提）。
* §2 `pW27_hslot_w_iff`：全 ∀ 形 ⟺ 诚实域形（`0 < j`）∧ j = 0 实例
  （纯逻辑拆分；j = 0 实例已被 §1 反证）⇒ v4 的 `hslot_w` 签名写 `0 < j`。
-/
import Kepler.Text.LocalFanStepW26

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 j = 0 实例反证 -/

/-- **`hslot_w` 在 j = 0 处的断言为假**：`ρ(ρ p) ∉ affGe {0}{p, ρ p}`
（`¬(vv 2 ∈ cone{p, vv 1})` 的可实例化反例形式）。 -/
theorem pW27_wslot_zero_false (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    (hk : 1 < V.ncard)
    (hnc : ¬ Collinear3 (0 : V3) p (vv 1))
    (haz : azim 0 (vv 1) (vv 2) p ≠ 0) :
    ¬ (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[1] p) ∈
        affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[1] p}) := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hvvV : ∀ n : ℕ, vv n ∈ V := fun n => by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  have hp0 : p ≠ (0 : V3) := fun h => h0V (h ▸ hp)
  have hv0 : vv 1 ≠ (0 : V3) := fun h => h0V (h ▸ hvvV 1)
  have hpv : p ≠ vv 1 := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 1 (by omega) hk
    rw [hiter 1, show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact fun h => hd h.symm
  have hnv : ¬ Collinear3 (0 : V3) (vv 1) p := by
    have h := hnc
    simp only [Collinear3] at h ⊢
    rwa [show ({0, p, vv 1} : Set V3) = ({0, vv 1, p} : Set V3) from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hnv2 : ¬ Collinear3 (0 : V3) (vv 1) (vv 2) := by
    have h := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf (hvvV 1)
    have e : rhoNode1_p2 FF (vv 1) = vv 2 := by
      rw [← hiter 1, ← hiter 2, show 2 = Nat.succ 1 from rfl]
      exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) 1 p).symm
    rwa [e] at h
  have e1 : (rhoNode1_p2 FF)^[1] p = vv 1 := hiter 1
  have e2 : rhoNode1_p2 FF (vv 1) = vv 2 := by
    rw [← hiter 1, ← hiter 2, show 2 = Nat.succ 1 from rfl]
    exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) 1 p).symm
  intro h
  rw [e1, e2, Set.pair_comm] at h
  exact haz ((azim_eq_zero_symm hnv2 hnv).mpr
    (pW6k6_azim_zero_of_affGe (a := vv 1) (x := p) (y := vv 2)
      hv0 hpv hp0 hnv h))

/-! ## §2 诚实域桥（全 ∀ 形 = `0 < j` 形 ∧ j = 0 实例） -/

/-- **`hslot_w` 诚实域 iff 桥**：全 ∀ 形 ⟺（`0 < j` 域形 ∧ j = 0 实例）。
结合 §1：j = 0 实例在一般配置下为假 ⇒ 诚实域恰为 `0 < j`（v4 签名依据）。 -/
theorem pW27_hslot_w_iff {p : V3} {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n) (k : ℕ) :
    (∀ j : ℕ, j + 2 < k →
        azim 0 ((rhoNode1_p2 FF)^[j + 1] p)
          (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j + 1] p)) p = 0)
      ↔ (∀ j : ℕ, 0 < j → j + 2 < k →
            azim 0 ((rhoNode1_p2 FF)^[j + 1] p)
              (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j + 1] p)) p = 0)
        ∧ (2 < k → azim 0 (vv 1) (vv 2) p = 0) := by
  have e1 : (rhoNode1_p2 FF)^[1] p = vv 1 := hiter 1
  have e2 : rhoNode1_p2 FF (vv 1) = vv 2 := by
    rw [← hiter 1, ← hiter 2, show 2 = Nat.succ 1 from rfl]
    exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) 1 p).symm
  constructor
  · intro h
    refine ⟨fun j _ hj => h j hj, fun h2 => ?_⟩
    have h0 := h 0 (by omega)
    rwa [show (0 : ℕ) + 1 = 1 from rfl, e1, e2] at h0
  · rintro ⟨ht, h0⟩ j hj
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · subst hz
      have h2 := h0 (by omega)
      rwa [show (0 : ℕ) + 1 = 1 from rfl, e1, e2]
    · exact ht j hpos hj

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW27_wslot_zero_false
#print axioms Kepler.Text.pW27_hslot_w_iff

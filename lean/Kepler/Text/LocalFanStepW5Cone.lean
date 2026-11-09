/-
Kepler/Text/LocalFanStepW5Cone.lean — wave C-W5Cone（W4b-i 的闭合关键件）。

HOL 锚：`NKEZBFC.hl:2242-2270`（`decomposition_planar_by_angle_fan` 第二析取的
收口段）+ `local_lemmas.hl:996` `FAN_IN_AFF_GE_IMP_EQ`。

本件交**第二析取不可能**的机器证明（`pW5_second_disjunct_false`）：
若 telescope 给出 `vv(j+2) ∈ affGe {0}{vv j1, vv(j1+1)}`（`j1 ≤ j`），则
* `{vv j1, vv(j1+1)} ∈ E`（轨道相邻 dart 的边）；
* `FAN_IN_AFF_GE_IMP_EQ`（LA5:1660，标准三）⇒ `vv(j+2) = vv j1 ∨ vv(j+2) = vv(j1+1)`；
* `LOFA_IMP_DIS_ELMS23`（LA5:7256，标准三）在 `j1 < j+2 < V.ncard` 下否定两者。
⇒ False。

**尚未交付**：`decomposition_planar_by_angle_fan` 的输入
`ρg ∈ affGe {0,v}{g}`（HOL 2223-2230 的锻造段；本波未定位其来源，
作为 DIFFERS 记账）。`pW5_flat_cone_order` 的总装 = 本件 + 该输入 + 第一析取。
-/
import Kepler.Text.LocalFanStepBW4

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 轨道点事实 -/

/-- 轨道相邻点的 rho 推进：`ρ(vv n) = vv (n+1)`。 -/
private theorem pW5c_rho_iter {v : V3} {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n) (n : ℕ) :
    rhoNode1_p2 FF (vv n) = vv (n + 1) := by
  rw [← hiter n, ← hiter (n + 1)]
  rw [show n + 1 = Nat.succ n from rfl, Function.iterate_succ_apply']

/-- **第二析取（展开形）不可能**：`vv(j+2) ∈ affGe {0}{vv j1, vv(j1+1)}` 且
`j1 ≤ j`、`j+2 < V.ncard` 时矛盾。 -/
theorem pW5_second_disjunct_false
    (hcl : convexLocalFan_p2 V E FF)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {j j1 : ℕ} (hj1 : j1 ≤ j) (hcard : j + 2 < V.ncard)
    (hmem : vv (j + 2) ∈ affGe ({0} : Set V3) {vv j1, vv (j1 + 1)}) :
    False := by
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := hcl.1
  have hVV : ∀ n, vv n ∈ V := by
    intro n
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv n
  -- 轨道相邻 dart 的边
  have hdart : (vv j1, rhoNode1_p2 FF (vv j1)) ∈ FF :=
    (LOCAL_FAN_RHO_NODE_PROS hcl.1).1 (vv j1) (hVV j1)
  rw [pW5c_rho_iter hiter j1] at hdart
  have hedge : ({vv j1, vv (j1 + 1)} : Set V3) ∈ E := by
    have h := LOCAL_FAN_IN_FF_IN_ORD_PAIRS hcl.1 hdart
    simpa [ordPairs_p2] using h
  -- FAN_IN_AFF_GE_IMP_EQ ⇒ 落到边端点
  have hfan_case := FAN_IN_AFF_GE_IMP_EQ (x := (0 : V3)) hfan (hVV (j + 2)) hedge hmem
  -- 两种情形都被 LOFA_IMP_DIS_ELMS23 否定
  have hne1 : vv (j + 2) ≠ vv j1 := by
    have := LOFA_IMP_DIS_ELMS23 hcl.1 hv j1 (j + 2) (by omega) hcard
    rwa [show (rhoNode1_p2 FF)^[j + 2] v = vv (j + 2) from hiter (j + 2),
      show (rhoNode1_p2 FF)^[j1] v = vv j1 from hiter j1] at this
  have hne2 : vv (j + 2) ≠ vv (j1 + 1) := by
    have := LOFA_IMP_DIS_ELMS23 hcl.1 hv (j1 + 1) (j + 2) (by omega) hcard
    rwa [show (rhoNode1_p2 FF)^[j + 2] v = vv (j + 2) from hiter (j + 2),
      show (rhoNode1_p2 FF)^[j1 + 1] v = vv (j1 + 1) from hiter (j1 + 1)] at this
  rcases hfan_case with h | h
  · exact hne1 h
  · exact hne2 h

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5_second_disjunct_false
#print axioms Kepler.Text.pW5_second_disjunct_false
#check @Kepler.Text.FAN_IN_AFF_GE_IMP_EQ
#print axioms Kepler.Text.FAN_IN_AFF_GE_IMP_EQ
#check @Kepler.Text.LOFA_IMP_DIS_ELMS23
#print axioms Kepler.Text.LOFA_IMP_DIS_ELMS23

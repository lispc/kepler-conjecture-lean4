/-
Kepler/Text/LocalFanStepW33.lean — wave W33：早一格排除（`pW5_second_disjunct_false`
的指数顺序无关化；full mirror hstep 的排除原语）。

HOL 对表（NKEZBFC.hl:2455–2583）：HOL 的第二析取排除用
`LOFA_IMP_EE_TWO_ELMS` + EE 集 + `LOFA_IMP_DIS_ELMS23`；本件的等价 Lean 原语
更短：**`FAN_IN_AFF_GE_IMP_EQ`（LocalAuto5:1660，std3）直接给出「点 ∈ 边锥 ⇒
点 = 边端点」**，与指数顺序无关——W32 Attempt 2 卡住的「早一格」实例只是
`pW5_second_disjunct_false`（W5Cone:41，std3）去掉 `j1 ≤ j` 守卫后的同一定理。
（该守卫在证明体中未被用于核心排除，仅用于 LOFA 互异性的 omega 定向。）

件目：
* §1 私有迭代桥（W5Cone 私有 `pW5c_rho_iter` 本地复制）。
* §2 `pW33_edge_cone_excl`：任意互异 run 指数 ⇒ `vv m ∉ affGe{0}{vv p1, vv(p1+1)}`。
* §3 `pW33_edge_cone_excl_mirror`：镜像实例（`m+1 ≤ p1`，早一格/更早）。
-/
import Kepler.Text.LocalFanStepW32

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 私有迭代桥 -/

/-- 复制件（源：`LocalFanStepW5Cone` 私有 `pW5c_rho_iter`）：`ρ(vv n) = vv(n+1)`。 -/
private theorem pW33_rho_iter {v : V3} {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n) (n : ℕ) :
    rhoNode1_p2 FF (vv n) = vv (n + 1) := by
  rw [← hiter n, ← hiter (n + 1)]
  rw [show n + 1 = Nat.succ n from rfl, Function.iterate_succ_apply']

/-! ## §2 早一格排除（一般形：指数顺序无关） -/

/-- **早一格排除（一般形）**：run 点 `vv m`（m ∉ {p1, p1+1}）不属于相邻对
`{vv p1, vv(p1+1)}` 的闭锥。任意指数顺序——含 W32 Attempt 2 卡住的
「点比相邻对早一格」（`m + 1 = p1`）与更早情形。
= `pW5_second_disjunct_false` 去掉 `j1 ≤ j` 守卫后的同一定理（证明体同一）。 -/
theorem pW33_edge_cone_excl (hcl : convexLocalFan_p2 V E FF)
    {v : V3} (hv : v ∈ V) {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {m p1 : ℕ} (hm : m < V.ncard) (hp1 : p1 + 1 < V.ncard)
    (hne1 : m ≠ p1) (hne2 : m ≠ p1 + 1)
    (hmem : vv m ∈ affGe ({0} : Set V3) {vv p1, vv (p1 + 1)}) :
    False := by
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := hcl.1
  have hVV : ∀ n : ℕ, vv n ∈ V := fun n => by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv n
  -- 相邻 dart 的边
  have hdart : (vv p1, rhoNode1_p2 FF (vv p1)) ∈ FF :=
    (LOCAL_FAN_RHO_NODE_PROS hcl.1).1 (vv p1) (hVV p1)
  rw [pW33_rho_iter hiter p1] at hdart
  have hedge : ({vv p1, vv (p1 + 1)} : Set V3) ∈ E := by
    have h := LOCAL_FAN_IN_FF_IN_ORD_PAIRS hcl.1 hdart
    simpa [ordPairs_p2] using h
  -- 边锥 ⇒ 端点
  have hcase := FAN_IN_AFF_GE_IMP_EQ (x := (0 : V3)) hfan (hVV m) hedge hmem
  -- 两端点均被互异性否定（任意指数序，LOFA 定向由 omega 选择）
  have hne_a : vv m ≠ vv p1 := by
    rcases Nat.lt_or_gt_of_ne hne1 with h | h
    · have hd := LOFA_IMP_DIS_ELMS23 hcl.1 hv m p1 h (by omega)
      rw [hiter m, hiter p1] at hd
      exact Ne.symm hd
    · have hd := LOFA_IMP_DIS_ELMS23 hcl.1 hv p1 m h hm
      rw [hiter p1, hiter m] at hd
      exact hd
  have hne_b : vv m ≠ vv (p1 + 1) := by
    rcases Nat.lt_or_gt_of_ne hne2 with h | h
    · have hd := LOFA_IMP_DIS_ELMS23 hcl.1 hv m (p1 + 1) h hp1
      rw [hiter m, hiter (p1 + 1)] at hd
      exact Ne.symm hd
    · have hd := LOFA_IMP_DIS_ELMS23 hcl.1 hv (p1 + 1) m h hm
      rw [hiter (p1 + 1), hiter m] at hd
      exact hd
  rcases hcase with h | h
  · exact hne_a h
  · exact hne_b h

/-! ## §3 镜像实例（早一格，供 full mirror hstep 直接消费） -/

/-- **早一格排除（镜像实例）**：`m + 1 ≤ p1`（点严格早于相邻对起点）时的
`¬ affGe` 形式——W32 Attempt 2 所需排除形的直接消费者。 -/
theorem pW33_edge_cone_excl_mirror (hcl : convexLocalFan_p2 V E FF)
    {v : V3} (hv : v ∈ V) {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {m p1 : ℕ} (hm1 : m + 1 ≤ p1) (hp1 : p1 + 1 < V.ncard) :
    vv m ∉ affGe ({0} : Set V3) {vv p1, vv (p1 + 1)} := by
  intro hmem
  exact pW33_edge_cone_excl hcl hv hiter (by omega) hp1 (by omega) (by omega) hmem

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW33_edge_cone_excl
#print axioms Kepler.Text.pW33_edge_cone_excl_mirror

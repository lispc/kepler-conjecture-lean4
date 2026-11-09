/-
Kepler/Text/LocalFanStepW5W4.lean — wave C-W5a-ii-3：`hprev` 的镜像路线探针（路线定型）。

本件把 w 侧 `hprev`（`vv n ∈ affGt{0}{v, vv(n-1)}`）的镜像分解在机器上实例化，
确定它**产出什么**：

* `pW5w4_decomp_at_prev`：以 (u := vv(n-1), w := vv n) 实例化
  `decomposition_planar_by_angle_fan`（Planarity:4203），前件全部由
  W5W2 的 2_1 桥（tip := ιv）与 BW4 的 `pW5b_affGt_subset_affGe` 供给；
  结论为
  `vv(n-1) ∈ affGt{0}{v, vv n} ∨ vv n ∈ affGe{0}{v, vv(n-1)}`。

**路线结论（与工单 §2 的判定配套）**：第一析取是**正向锥形**（`hstep(n-1)`），
**不是** `hprev(n)`；第二析取是闭 1_2 锥（其否定不能由指标计数得到，见 W5W2 §2(b)）。
因此「镜像 decomposition」路线**不直接产出 `hprev`**——`hprev` 需要 azim/径向序
论证（DELIVERY §3 的推荐路线）。本件不引入公理/ sorry，只定型。
-/
import Kepler.Text.LocalFanStepW5W2
import Kepler.Text.LocalFanStepW5W3

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **w 侧镜像分解的机器实例**：前件齐备，结论为
「正向锥形 at n-1 ∨ 闭 1_2 锥 at n」。 -/
theorem pW5w4_decomp_at_prev
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {n : ℕ} (hn2 : 2 ≤ n) (hnk : n ≤ V.ncard - 1)
    (hprev1 : vv (n - 1) ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v})
    (hn2c : vv n ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v})
    (hne0 : vv (n - 1) ≠ 0) (hnev : vv (n - 1) ≠ v)
    (hnc_prev : ¬ Collinear3 (0 : V3) v (vv (n - 1)))
    (hnc_n : ¬ Collinear3 (0 : V3) v (vv n)) :
    vv (n - 1) ∈ affGt ({0} : Set V3) {v, vv n}
      ∨ vv n ∈ affGe ({0} : Set V3) {v, vv (n - 1)} := by
  have h21 : vv n ∈ affGt ({0, v} : Set V3) {vv (n - 1)} :=
    pW5w2_affGt_prev_21 hcl hv hiter (by omega) hnk hprev1 hn2c hne0 hnev
  have hge : vv n ∈ affGe ({0, v} : Set V3) {vv (n - 1)} :=
    pW5b_affGt_subset_affGe h21
  exact decomposition_planar_by_angle_fan (x := (0 : V3)) (v := v)
    (u := vv (n - 1)) (w := vv n) hnc_prev hnc_n hge

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w4_decomp_at_prev
#print axioms Kepler.Text.pW5w4_decomp_at_prev

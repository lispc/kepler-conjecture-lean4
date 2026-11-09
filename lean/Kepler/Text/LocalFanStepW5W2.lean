/-
Kepler/Text/LocalFanStepW5W2.lean — wave C-W5a-ii（第一步）：w 侧反向锥形的 2_1 形桥。

本件只交 `hprev` 推导链的第一块（可独立落库）：

* `pW5w2_affGt_prev_21`：w 侧 flat-run 半平面（`vv(n-1), vv n ∈ affGt{0,v}{ιv}`）
  ⇒ `vv n ∈ affGt {0,v}{vv(n-1)}`（**2_1 形**，v 系数自由）。
  直接套 `pW5b_affGt_halfplane_transfer`（BW5ConeB，tip := ιv），
  `x := 0, b := v, c := ιv, a := vv(n-1), y := vv n`。

**未交**：把 2_1 升级到 `hprev` 所需的 1_2 形 `vv n ∈ affGt{0}{v, vv(n-1)}`
（v 系数也要正）。两条路线评估见 DELIVERY §3（换序路线不免费；
`pW5_second_disjunct_false` 的镜像**不能**直接套——指标计数不撞）。
-/
import Kepler.Text.LocalFanStepW5W
import Kepler.Text.LocalFanStepW5ConeB

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **w 侧反向锥形的 2_1 形桥**：flat-run（tip `ιv`）+ 互异 ⇒
`vv n ∈ affGt {0,v}{vv(n-1)}`（v 系数自由）。 -/
theorem pW5w2_affGt_prev_21
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ V.ncard - 1)
    (hprev1 : vv (n - 1) ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v})
    (hn : vv n ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v})
    (hne0 : vv (n - 1) ≠ 0) (hnev : vv (n - 1) ≠ v) :
    vv n ∈ affGt ({0, v} : Set V3) {vv (n - 1)} := by
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hιV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hcl.1 hv
  have hιne0 : ivsRhoNode1_p2 FF v ≠ 0 := fun h => h0V (h ▸ hιV)
  have hιnev : ivsRhoNode1_p2 FF v ≠ v := by
    intro h
    exact (LOFA_IMP_NOT_COLL_IVS hcl.1 hv) (by
      rw [h]; exact collinear3_pair_right rfl)
  have h0v : (0 : V3) ≠ v := fun h => h0V (h ▸ hv)
  exact pW5b_affGt_halfplane_transfer (x := (0 : V3)) (b := v)
    (c := ivsRhoNode1_p2 FF v) (a := vv (n - 1)) (y := vv n)
    h0v hιne0 hιnev hne0 hnev hprev1 hn

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w2_affGt_prev_21
#print axioms Kepler.Text.pW5w2_affGt_prev_21

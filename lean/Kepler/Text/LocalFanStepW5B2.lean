/-
Kepler/Text/LocalFanStepW5B2.lean — wave C-W5b-ii：w 侧 dart 级包含（核心几何件）。

件目（1 件 + 1 用法例）：
* `pW5b2_rho_mem`：w 侧相邻轨道点 `g := vv n`、`ρg := vv(n+1)` 都在
  `affGt{0,v}{ιv}`（`pW5b_flat_mem`）⇒ 半平面传递（tip := `ιv`，2_1 形）
  ⇒ `ρg ∈ affGt{0,v}{g}` ⇒ `affGe{0,v}{g}`。
  这是 u 侧 HOL 2194-2270 的 `ρg ∈ affGe{0,v}{g}` 的 w 侧镜像；
  与 `pW5w_telescope`（`hprev` 显式槽）的并集展开逐字对齐
  （指标方向 `vv(V.ncard - j1 - 1)` 不在本件换序）。
* `pW5b2_dart_affGe`：同一事实的 `affGe` 直接形（供 W6 装配直接引用）。
-/
import Kepler.Text.LocalFanStepW5B

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **w 侧 dart 级核心**：`i+1 ≤ n`、`n+1 ≤ k-1` ⇒
`vv(n+1) ∈ affGt {0,v}{vv n}`（ρg 在半平面锥内）。 -/
theorem pW5b2_rho_mem
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k - 1) (hbi : bta (i + 1) = bta (k - 1))
    {n : ℕ} (hn1 : i + 1 ≤ n) (hnk : n + 1 ≤ k - 1) :
    vv (n + 1) ∈ affGt ({0, v} : Set V3) {vv n} := by
  have hl : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ m, vv m ∈ V := by
    intro m
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hl hv m
  have hg_n : vv n ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v} :=
    pW5b_flat_mem hcl hg hv hk hiter hbta hi hbi hn1 (by omega)
  have hg_n1 : vv (n + 1) ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v} :=
    pW5b_flat_mem hcl hg hv hk hiter hbta hi hbi (by omega) (by omega)
  have h0v : (0 : V3) ≠ v := fun h => h0V (h ▸ hv)
  have hιV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V hl hv
  have hι0 : ivsRhoNode1_p2 FF v ≠ 0 := fun h => h0V (h ▸ hιV)
  have hιv : ivsRhoNode1_p2 FF v ≠ v := by
    intro h
    exact (LOFA_IMP_NOT_COLL_IVS hl hv) (by
      rw [h]; exact collinear3_pair_right rfl)
  have hvvn0 : vv n ≠ 0 := fun h => h0V (h ▸ hVV n)
  have hvvnv : vv n ≠ v := by
    have hdis := LOFA_IMP_DIS_ELMS23 hl hv 0 n (by omega) (by omega)
    rw [show (rhoNode1_p2 FF)^[0] v = v from by simp] at hdis
    rw [show (rhoNode1_p2 FF)^[n] v = vv n from hiter n] at hdis
    exact fun h => hdis h
  exact pW5b_affGt_halfplane_transfer (x := (0 : V3)) (b := v)
    (c := ivsRhoNode1_p2 FF v) (a := vv n) (y := vv (n + 1))
    h0v hι0 hιv hvvn0 hvvnv hg_n hg_n1

/-- **w 侧 dart 级包含（affGe 形）**：同前件的闭锥版本。 -/
theorem pW5b2_dart_affGe
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k - 1) (hbi : bta (i + 1) = bta (k - 1))
    {n : ℕ} (hn1 : i + 1 ≤ n) (hnk : n + 1 ≤ k - 1) :
    vv (n + 1) ∈ affGe ({0, v} : Set V3) {vv n} :=
  pW5b_affGt_subset_affGe
    (pW5b2_rho_mem hcl hg hv hk hiter hbta hi hbi hn1 hnk)

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5b2_rho_mem
#print axioms Kepler.Text.pW5b2_rho_mem
#check @Kepler.Text.pW5b2_dart_affGe
#print axioms Kepler.Text.pW5b2_dart_affGe

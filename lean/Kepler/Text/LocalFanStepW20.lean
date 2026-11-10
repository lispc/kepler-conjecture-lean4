/-
Kepler/Text/LocalFanStepW20.lean — wave W20：望远镜 endgame 侦察件包（消槽前的减半）。

交班记录复读结论（W5W2/W5W3/W5W4）：
* hprev 的 1_2 形 ⟺ 两个 2_1 合取（`pW5w3_one_two_iff`）；C1 =
  `vv n ∈ affGt{0,v}{vv(n-1)}` 已由 `pW5w2_affGt_prev_21` 给；**C2 =
  `vv n ∈ affGt{0,vv(n-1)}{v}`（v 系数正半）为在案硬点**（估 80–140，
  `FAN_IN_AFF_GE_IMP_EQ` 边界排除路线已判不可行，W5W3 判定）。
* 新发现：pW19 的 hprev 槽从 n = 1 起即退化（`{v, vv 0} = {v}` 单点 t-set
  ⇒ 要求 `vv 1` 在 v 射线上）⇒ **槽的诚实范围是 n ≥ 2**（形式反证见 §3）。

件目：
* §1 `pW20_hprev_iff_21`：hprev 1_2 形 = C1 ∧ C2（one_two_iff 实例）。
* §2 `pW20_c2_iff_azim`：C2 ⟺ `azim 0 (vv(n-1)) v (vv n) = 0`（iff_alt 实例）。
* §3 `pW20_hprev_one_degenerate`：pW19 hprev 槽 n = 1 实例的反证（槽范围更正）。
-/
import Kepler.Text.LocalFanStepW19
import Kepler.Text.LocalFanStepW5W3

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 hprev 的 2_1 分解 -/

/-- `hprev` 的 1_2 形 = 两个 2_1 合取（`pW5w3_one_two_iff` 在 `x := 0` 的实例）。 -/
theorem pW20_hprev_iff_21 {v a y : V3} (hnc : ¬ Collinear3 (0 : V3) v a) :
    y ∈ affGt ({0} : Set V3) {v, a}
      ↔ y ∈ affGt ({0, v} : Set V3) {a} ∧ y ∈ affGt ({0, a} : Set V3) {v} :=
  pW5w3_one_two_iff (x := (0 : V3)) hnc

/-! ## §2 C2 的 azim 归约 -/

/-- C2 半（`y ∈ affGt{0,a}{v}`）⟺ 径向零点 `azim 0 a v y = 0`
（`azim_eq_zero_iff_alt` 实例；非退化前提取自扇/generic）。 -/
theorem pW20_c2_iff_azim {a v y : V3}
    (hncav : ¬ Collinear3 (0 : V3) a v) (hncay : ¬ Collinear3 (0 : V3) a y) :
    y ∈ affGt ({0, a} : Set V3) {v} ↔ azim 0 a v y = 0 :=
  (azim_eq_zero_iff_alt (v0 := (0 : V3)) (v1 := a) (w := v) (x := y) hncav hncay).symm

/-! ## §3 hprev 槽 n = 1 退化反证（槽范围更正证据） -/

/-- **pW19 hprev 槽在 n = 1 的实例不可证**：`vv 1 ∈ affGt {0}{p, vv 0}` 迫使
`vv 1` 落在 p 射线上（单点 t-set 退化），与 generic 非共线矛盾。
⇒ 诚实槽范围从 n = 2 起。 -/
theorem pW20_hprev_one_degenerate (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    (hnc : ¬ Collinear3 (0 : V3) p (vv 1))
    (h1 : vv 1 ∈ affGt ({0} : Set V3) {p, vv (1 - 1)}) :
    False := by
  have hp0 : (0 : V3) ≠ p :=
    fun h => (CVLF_LF_F hcl).2.2.2.2.1 (h.symm ▸ hp)
  have hv0 : vv 0 = p := by
    have h := hiter 0
    simpa using h.symm
  have h1' : vv 1 ∈ affGt ({0} : Set V3) {p, p} := by
    rw [show 1 - 1 = 0 from rfl, hv0] at h1
    exact h1
  have hset : ({p, p} : Set V3) = ({p} : Set V3) := by
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at h1'
  obtain ⟨f, hfin, hsumV, hpos, hsum⟩ := h1'
  have h3 : hfin.toFinset = ({0, p} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  rw [h3, Finset.sum_insert (by simp [hp0]), Finset.sum_singleton] at hsumV
  simp only [smul_zero, zero_add] at hsumV
  have hfp : 0 < f p := hpos p (by simp)
  apply hnc
  rw [collinear3_iff_smul (v := (0 : V3)) (w := p) (w1 := vv 1) (Ne.symm hp0)]
  refine ⟨f p, ?_⟩
  rw [hsumV]
  module

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW20_hprev_iff_21
#print axioms Kepler.Text.pW20_c2_iff_azim
#print axioms Kepler.Text.pW20_hprev_one_degenerate

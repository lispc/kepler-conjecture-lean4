/-
Kepler/Text/LocalFanStepW5ConeB.lean — wave C-W5ConeB：`pW5_flat_cone_order` 总装。

三块：
* §1 `pW5b_affGt_halfplane_transfer`（半平面传递，通用件）：
  `a, y ∈ affGt {x}{b,c}`（x,b,c 非共线）⇒ `y ∈ affGt {x,b}{a}`。
  路线：`aff_gt_inter_aff_gt` 取 2_1 形，`affGt_pair_iff` 两次 + 代数
  （c-x = (1/t3)(a-x) - (t2/t3)(b-x)，代入 y 的分解）。
* §1' `pW5b_affGt_subset_affGe`：`affGt ⊆ affGe`（Affsign 签名放宽）。
* §2 `pW5b_hstep`（强归纳）：`hstep(n)` 用较小指标（`i := n`, `j := n-1`）的
  telescope 展开第二析取，交 `pW5_second_disjunct_false` 否定；第一析取即结论。
* §3 `pW5_flat_cone_order`：对外形（flat-run 半平面 + 非共线 ⇒ 锥形）。
-/
import Kepler.Text.LocalFanStepBW4
import Kepler.Text.LocalFanStepW5Cone

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 半平面传递（通用件） -/

/-- **半平面传递**：`a, y ∈ affGt {x,b}{c}`（2_1 形）⇒ `y ∈ affGt {x,b}{a}`
（a 系数正、b 系数自由）。`affGt_pair_iff` 两次 + 代数。 -/
theorem pW5b_affGt_halfplane_transfer {x b c a y : V3}
    (hxb : x ≠ b) (hcx : c ≠ x) (hcb : c ≠ b) (hax : a ≠ x) (hab : a ≠ b)
    (ha : a ∈ affGt ({x, b} : Set V3) {c})
    (hy : y ∈ affGt ({x, b} : Set V3) {c}) :
    y ∈ affGt ({x, b} : Set V3) {a} := by
  obtain ⟨t3, ht3, t2, hda⟩ :=
    (affGt_pair_iff (v0 := x) (v1 := b) (x := c) (y := a) hxb hcx hcb).mp ha
  obtain ⟨s3, hs3, s2, hdy⟩ :=
    (affGt_pair_iff (v0 := x) (v1 := b) (x := c) (y := y) hxb hcx hcb).mp hy
  refine (affGt_pair_iff (v0 := x) (v1 := b) (x := a) (y := y) hxb hax hab).mpr ?_
  refine ⟨s3 / t3, div_pos hs3 ht3, s2 - s3 * t2 / t3, ?_⟩
  have hcx_eq : c - x = (1 / t3) • (a - x) - (t2 / t3) • (b - x) := by
    have h1 : t3 • (c - x) = (a - x) - t2 • (b - x) := by
      rw [hda]
      abel
    calc c - x = (1 / t3) • (t3 • (c - x)) := by
          rw [smul_smul, one_div_mul_cancel ht3.ne', one_smul]
      _ = (1 / t3) • ((a - x) - t2 • (b - x)) := by rw [h1]
      _ = (1 / t3) • (a - x) - (t2 / t3) • (b - x) := by
          rw [smul_sub, smul_smul]
          congr 2
          field_simp
  rw [hdy, hcx_eq, smul_sub, smul_smul, smul_smul]
  module

/-- `affGt ⊆ affGe`（Affsign 签名放宽）。 -/
theorem pW5b_affGt_subset_affGe {s t : Set V3} :
    affGt s t ⊆ affGe s t := by
  intro z hz
  have hz' : Affsign (fun r => 0 < r) s t z := hz
  show Affsign (fun r => 0 ≤ r) s t z
  obtain ⟨f, hfin, hval, hpos, hone⟩ := hz'
  exact ⟨f, hfin, hval, fun w hw => le_of_lt (hpos w hw), hone⟩

/-! ## §2 `hstep` 的强归纳 -/

/-- **`hstep` 强归纳**：flat-run（`vv m ∈ affGt{0,v}{ρv}`，`1≤m≤i`）+
逐点非共线（`1≤m≤i+1`）⇒ 锥形序（`n+1 ≤ i`）。 -/
theorem pW5b_hstep
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {i : ℕ} (hik : i < V.ncard)
    (hflat : ∀ n, 1 ≤ n → n ≤ i → vv n ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v})
    (hnc : ∀ n, 1 ≤ n → n ≤ i + 1 → ¬ Collinear3 (0 : V3) v (vv n)) :
    ∀ n, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {v, vv (n + 1)} := by
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ n, vv n ∈ V := by
    intro n
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv n
  have hρV : rhoNode1_p2 FF v ∈ V := by
    have h := LOCAL_FAN_ITER_RHO_NODE_IN_V hcl.1 hv 1
    simpa using h
  have hρne0 : rhoNode1_p2 FF v ≠ 0 := fun h => h0V (h ▸ hρV)
  have hρnev : rhoNode1_p2 FF v ≠ v := by
    intro h
    exact (LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hcl.1 hv) (by
      rw [h]; exact collinear3_pair_right rfl)
  have hncρ : ¬ Collinear3 (0 : V3) v (rhoNode1_p2 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hcl.1 hv
  have h0v : (0 : V3) ≠ v := fun h => h0V (h ▸ hv)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hni
    have hncard : n < V.ncard := by omega
    have hprem : ∀ m, 0 < m → m + 1 ≤ n → vv m ∈ affGt ({0} : Set V3) {v, vv (m + 1)} := by
      intro m hm0 hmn
      exact ih m (by omega) hm0 (by omega)
    have hj : n - 1 < n := by omega
    have htel := pW4_telescope_u hcl hv hiter hprem (n - 1) hj
    have htel' : ∀ z : V3, z ∈ affGe ({0} : Set V3) {v, vv n}
        ↔ ∃ j1, j1 ≤ n - 1 ∧ z ∈ affGe ({0} : Set V3) {vv j1, vv (j1 + 1)} := by
      have hidx : n - 1 + 1 = n := by omega
      intro z
      rw [← hidx]
      exact htel z
    -- 半平面传递 ⇒ 分解第二前提
    have hg_n : vv n ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v} :=
      hflat n (by omega) (by omega)
    have hg_n1 : vv (n + 1) ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v} :=
      hflat (n + 1) (by omega) (by omega)
    have hvvn0 : vv n ≠ 0 := fun h => h0V (h ▸ hVV n)
    have hvvnv : vv n ≠ v := by
      have hdis := LOFA_IMP_DIS_ELMS23 hcl.1 hv 0 n (by omega) hncard
      rw [show (rhoNode1_p2 FF)^[0] v = v from by simp] at hdis
      rw [show (rhoNode1_p2 FF)^[n] v = vv n from hiter n] at hdis
      exact fun h => hdis h
    have hnc_n : ¬ Collinear3 (0 : V3) v (vv n) := hnc n (by omega) (by omega)
    have hnc_n1 : ¬ Collinear3 (0 : V3) v (vv (n + 1)) := hnc (n + 1) (by omega) (by omega)
    have htrans := pW5b_affGt_halfplane_transfer (x := (0 : V3)) (b := v)
      (c := rhoNode1_p2 FF v) (a := vv n) (y := vv (n + 1))
      h0v hρne0 hρnev hvvn0 hvvnv hg_n hg_n1
    have hge : vv (n + 1) ∈ affGe ({0, v} : Set V3) {vv n} :=
      pW5b_affGt_subset_affGe htrans
    -- 平面分解
    have hdec := decomposition_planar_by_angle_fan (x := (0 : V3)) (v := v)
      (u := vv n) (w := vv (n + 1)) hnc_n hnc_n1 hge
    rcases hdec with h | h
    · exact h
    · have hmem := (htel' (vv (n + 1))).mp h
      obtain ⟨j1, hj1, hz⟩ := hmem
      exact (pW5_second_disjunct_false hcl hv hiter (j := n - 1) (j1 := j1)
        hj1 (by omega)
        (by simpa [show (n - 1) + 2 = n + 1 from by omega] using hz)).elim

/-! ## §3 对外形 -/

/-- **`pW5_flat_cone_order`**：flat-run 半平面（`vv n, vv(n+1) ∈ affGt{0,v}{ρv}`，
`0<n`、`n+1≤i`）+ 非共线 ⇒ `vv n ∈ affGt {0}{v, vv(n+1)}`（锥形）。 -/
theorem pW5_flat_cone_order
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n)
    {i : ℕ} (hik : i < V.ncard)
    (hflat : ∀ n, 0 < n → n ≤ i → vv n ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v})
    (hnc : ∀ n, 0 < n → n ≤ i + 1 → ¬ Collinear3 (0 : V3) v (vv n)) :
    ∀ n, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {v, vv (n + 1)} :=
  pW5b_hstep hcl hv hiter hik
    (fun m hm1 hmi => hflat m (by omega) hmi)
    (fun m hm1 hmi1 => hnc m (by omega) hmi1)

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5b_affGt_halfplane_transfer
#print axioms Kepler.Text.pW5b_affGt_halfplane_transfer
#check @Kepler.Text.pW5b_hstep
#print axioms Kepler.Text.pW5b_hstep
#check @Kepler.Text.pW5_flat_cone_order
#print axioms Kepler.Text.pW5_flat_cone_order

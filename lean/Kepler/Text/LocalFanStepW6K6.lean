/-
Kepler/Text/LocalFanStepW6K6.lean — wave C-W6-K6 patch A：azim↔int 识别式 + 配套桥。

路线勘误（工单 ① azim_add 项）：**不需要 azim_add**——库内公开件
`azim_eq_azim_iff`（AzimLemmas:193，HOL AZIM_EQ flyspeck.ml:2522）
`azim v0 v1 w x = azim v0 v1 w y ↔ y ∈ affGt {v0,v1} {x}` 即测角参数替换器，
配合 `azim_compl`（换序）与 `azim_eq_zero_iff/_alt`（径向零点⇔锥成员）
即可完成全部替换链，三段识别全部收敛为成员性 iff。

件目：
* §1 私有件公开复制：`exp_add_pi`（LuneVolume:856）、`zOf_eq_zero_iff_axis`
  （LuneVolume:247）、`mem_affineSpan_triple_of_eq`（LuneVolume:694）。
* §2 `pW6k6_coplanar_of_azim_pi`：LuneVolume:869 private 版公开复制
  （azim = π ⇒ 四点共面；工单 ③）。
* §3 `pW6k6_azim_zero_of_affGe`：closed-cone 径向零点——
  `y ∈ affGe {0} {a,x} ⇒ azim 0 a x y = 0`（工单 ② 的 affGe 边界退化归零）。
* §4 `pW6k6_iter_ivs`：`ι(vv n) = vv(n−1)`（0 < n；IVS_RHO_IDD）。
* §5 `pW6k6_identification`：azim↔int 三段识别式（工单 ② 主件；ρ(w)/ι(u)
  望远镜步以 azim 零点形式显式槽化）。
-/
import Kepler.Text.LocalFanStepW6K5
import Kepler.Text.LocalFanStepW5B
import Kepler.Text.LocalFanStepW6K4

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 私有件公开复制 -/

/-- LuneVolume:856 private 版公开复制（逐字模式）。 -/
private theorem pW6k6_exp_add_pi (ψ : ℝ) :
    Complex.exp (((ψ + Real.pi : ℝ) : ℂ) * Complex.I)
      = -Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hsplit : (((ψ + Real.pi : ℝ)) : ℂ) * Complex.I
      = ((ψ : ℝ) : ℂ) * Complex.I + Complex.I * ((Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hsplit, Complex.exp_add, hpi]
  ring

/-- LuneVolume:247 private 版公开复制（逐字模式）。 -/
theorem pW6k6_zOf_eq_zero_iff_axis {v w e1 e2 e3 : V3}
    (he : Orthonormal3 e1 e2 e3) (hax : (w - v : V3) = dist w v • e3) (hw : w ≠ v)
    (z : V3) : zOf e1 e2 z = 0 ↔ ∃ c : ℝ, z = c • (w - v) := by
  constructor
  · intro hz
    have hcol : Collinear3 v w (v + z) := by
      by_contra hnc
      exact (zOf_ne_zero_iff he hax hw (v + z)).mpr hnc (by simpa using hz)
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hw).mp hcol
    exact ⟨c, by simpa using hc⟩
  · rintro ⟨c, rfl⟩
    rw [zOf_smul, zOf_axis hax he, mul_zero]

/-- LuneVolume:694 private 版公开复制（逐字模式）。 -/
theorem pW6k6_mem_affineSpan_triple_of_eq {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (q - x) + h • (p - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : c • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd4 : h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd5 : c • (q - x) + h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval : y = h • (p - x) +ᵥ (c • (q - x) +ᵥ x) := by
    rw [hy, vadd_eq_add, vadd_eq_add]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd4
    (AffineSubspace.vadd_mem_of_mem_direction hd3 hxS)

/-! ## ## §2 azim = π ⇒ 共面（LuneVolume:869 公开复制） -/

/-- LuneVolume:869 private 版公开复制（逐字模式）：`azim z w w1 w2 = π` 时
四点共面。 -/
theorem pW6k6_coplanar_of_azim_pi {z w w1 w2 : V3}
    (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2)
    (hpi : azim z w w1 w2 = Real.pi) :
    Coplanar ({z, w, w1, w2} : Set V3) := by
  have hwv : w ≠ z := fun he => h1 (collinear3_of_eq he)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (w - z) (sub_ne_zero.mpr hwv)
  have hax : (w - z : V3) = dist w z • e3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec h1 h2 hon hax hwv
  have hr1ne : ((r1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr1.ne'
  have hz2' : zOf e1 e2 (w2 - z) = -(((r2 / r1 : ℝ) : ℂ) * zOf e1 e2 (w1 - z)) := by
    rw [hz1, hz2, hpi, pW6k6_exp_add_pi]
    push_cast
    field_simp [hr1ne]
  have hzero : zOf e1 e2 (w2 - z + ((r2 / r1 : ℝ) • (w1 - z))) = 0 := by
    rw [zOf_add, zOf_smul, hz2']
    ring
  obtain ⟨c, hc⟩ := (pW6k6_zOf_eq_zero_iff_axis hon hax hwv _).mp hzero
  have hc' : w2 - z = (-(r2 / r1)) • (w1 - z) + c • (w - z) := by
    rw [← hc]; module
  have hw2span : w2 ∈ affineSpan ℝ ({z, w, w1} : Set V3) := by
    refine pW6k6_mem_affineSpan_triple_of_eq (x := z) (p := w) (q := w1)
      (c := -(r2 / r1)) (h := c) ?_
    rw [show w2 = (w2 - z) + z by abel, hc']
    abel
  refine ⟨z, w, w1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact hw2span

/-! ## ## §3 closed-cone 径向零点 -/

/-- 单点并两点集 toFinset 求和分解（Aff.lean:59 private 模式、并集顺序对齐
Affsign 的 s ∪ t）。 -/
private theorem pW6k6_sum_pair {f : V3 → ℝ} {a p q : V3}
    (hap : a ≠ p) (haq : a ≠ q) (hpq : p ≠ q)
    (hfin : ({a} ∪ {p, q} : Set V3).Finite) :
    ∑ w ∈ hfin.toFinset, f w = f a + f p + f q := by
  have h3 : hfin.toFinset = ({a, p, q} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hap, haq]), Finset.sum_insert (by simp [hpq]),
    Finset.sum_singleton]
  ring

/-- 单点并两点集 toFinset 向量和分解（Aff.lean:70 private 模式、并集顺序对齐
Affsign 的 s ∪ t）。 -/
private theorem pW6k6_sum_pair_v {f : V3 → ℝ} {a p q : V3}
    (hap : a ≠ p) (haq : a ≠ q) (hpq : p ≠ q)
    (hfin : ({a} ∪ {p, q} : Set V3).Finite) :
    ∑ w ∈ hfin.toFinset, f w • w = f a • a + f p • p + f q • q := by
  have h3 : hfin.toFinset = ({a, p, q} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hap, haq]), Finset.sum_insert (by simp [hpq]),
    Finset.sum_singleton]
  abel

/-- **closed-cone 径向零点**（HOL AZIM_EQ_0_GE 对应）：`y ∈ affGe {0} {a,x}` 给
`azim 0 a x y = 0`（内点走 iff_alt、边界 y = β•a 走退化约定）。 -/
theorem pW6k6_azim_zero_of_affGe {a x y : V3} (ha0 : a ≠ 0) (hax : x ≠ a)
    (hx0 : x ≠ 0) (hnc : ¬ Collinear3 (0 : V3) a x)
    (hmem : y ∈ affGe ({0} : Set V3) {a, x}) :
    azim 0 a x y = 0 := by
  obtain ⟨f, hfin, hsumV, hpos, hsum⟩ := hmem
  have hap : (0 : V3) ≠ a := Ne.symm ha0
  have haq : (0 : V3) ≠ x := Ne.symm hx0
  rw [pW6k6_sum_pair_v hap haq (Ne.symm hax) hfin] at hsumV
  simp only [smul_zero, zero_add] at hsumV
  have hfx : 0 ≤ f x := hpos x (by simp)
  rcases lt_or_eq_of_le hfx with hγ | hγ
  · have hmemGt : y ∈ affGt ({0, a} : Set V3) {x} := by
      rw [affGt_pair_iff (v0 := (0 : V3)) (v1 := a) (x := x) (y := y) hap hx0 hax]
      refine ⟨f x, hγ, f a, ?_⟩
      rw [hsumV]
      module
    have hncY : ¬ Collinear3 (0 : V3) a y := aff_gt_imp_not_collinear hnc hmemGt
    exact (azim_eq_zero_iff_alt hnc hncY).mpr hmemGt
  · rw [← hγ] at hsumV
    simp only [zero_smul] at hsumV
    have hcol : Collinear3 (0 : V3) a y := by
      rw [collinear3_iff_smul (v := (0 : V3)) (w := a) (w1 := y) ha0]
      refine ⟨f a, ?_⟩
      rw [hsumV]
      module
    rw [azim, if_pos (Or.inr hcol)]

/-! ## ## §4 ι-iter 件 -/

/-- `ι(vv n) = vv(n−1)`（`0 < n`；由 `IVS_RHO_IDD` 与迭代一致性）。 -/
theorem pW6k6_iter_ivs (hlf : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n) {n : ℕ} (hn : 0 < n) :
    ivsRhoNode1_p2 FF (vv n) = vv (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hin : vv m ∈ V := by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hv m
  have h1 : ivsRhoNode1_p2 FF (rhoNode1_p2 FF (vv m)) = vv m := IVS_RHO_IDD hlf hin
  have h2 : rhoNode1_p2 FF (vv m) = vv (m + 1) := by
    rw [← hiter m, ← hiter (m + 1), Function.iterate_succ_apply']
  rw [h2] at h1
  exact h1

/-! ## ## §5 azim↔int 三段识别式 -/

/-- **W6-K6 ②主件**：azim↔int 识别式。望远镜步以径向零点显式槽化：
`hS3 : azim 0 u ι(u) v = 0`、`hS4 : azim 0 w ρ(w) v = 0`
（affGe 成员 ⇒ 径向零点由 §3；成员本身 = hprev 槽，下一波总装）。 -/
theorem pW6k6_identification
    (hlf : localFan_p2 V E FF) {v u w : V3} (hv : v ∈ V) (hu : u ∈ V) (hw : w ∈ V)
    (hrho : rhoNode1_p2 FF u = w)
    (hivs : ivsRhoNode1_p2 FF w = u)
    (hM1 : u ∈ affGt ({0, v} : Set V3) {rhoNode1_p2 FF v})
    (hM2 : w ∈ affGt ({0, v} : Set V3) {ivsRhoNode1_p2 FF v})
    (hS3 : azim 0 u (ivsRhoNode1_p2 FF u) v = 0)
    (hS4 : azim 0 w (rhoNode1_p2 FF w) v = 0)
    (hcop : ¬ Coplanar ({0, v, u, w} : Set V3)) :
    interiorAngle1_p2 0 FF v = azim 0 v u w
      ∧ interiorAngle1_p2 0 FF u = azim 0 u w v
      ∧ interiorAngle1_p2 0 FF w = azim 0 w v u := by
  have hρv : ¬ Collinear3 (0 : V3) v (rhoNode1_p2 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hv
  have hιv : ¬ Collinear3 (0 : V3) v (ivsRhoNode1_p2 FF v) := LOFA_IMP_NOT_COLL_IVS hlf hv
  have hρu : ¬ Collinear3 (0 : V3) u (rhoNode1_p2 FF u) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hu
  have hιu : ¬ Collinear3 (0 : V3) u (ivsRhoNode1_p2 FF u) := LOFA_IMP_NOT_COLL_IVS hlf hu
  have hρw : ¬ Collinear3 (0 : V3) w (rhoNode1_p2 FF w) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hw
  have hιw : ¬ Collinear3 (0 : V3) w (ivsRhoNode1_p2 FF w) := LOFA_IMP_NOT_COLL_IVS hlf hw
  have heq1 : ({0, u, w, v} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have heq2 : ({0, v, w, u} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have heq3 : ({0, u, v, w} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have heq4 : ({0, w, v, u} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have heq5 : ({0, w, u, v} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have nCvw : ¬ Collinear3 (0 : V3) v w :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (pW6k5_notCoplanar_congr heq2 hcop)
  have nCvu : ¬ Collinear3 (0 : V3) v u :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (x := v) (y := u) (z := w) hcop
  have nCuw : ¬ Collinear3 (0 : V3) u w :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (pW6k5_notCoplanar_congr heq1 hcop)
  have nCuv : ¬ Collinear3 (0 : V3) u v :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (pW6k5_notCoplanar_congr heq3 hcop)
  have nCwv : ¬ Collinear3 (0 : V3) w v :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (pW6k5_notCoplanar_congr heq4 hcop)
  have nCwu : ¬ Collinear3 (0 : V3) w u :=
    pW6k5_notCollinear3_0_of_notCoplanar4 (pW6k5_notCoplanar_congr heq5 hcop)
  -- v 项：ι(v)→w（iff 直接），ρ(v)→u（compl 对）
  have iff1 : azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)
      = azim 0 v (rhoNode1_p2 FF v) w := (azim_eq_azim_iff hρv hιv nCvw).mpr hM2
  have iff4 : azim 0 v w (rhoNode1_p2 FF v) = azim 0 v w u :=
    (azim_eq_azim_iff nCvw hρv nCvu).mpr hM1
  have c1 := azim_compl nCvw hρv
  have c2 := azim_compl nCvw nCvu
  rw [← iff4] at c2
  have hvpart : interiorAngle1_p2 0 FF v = azim 0 v u w := by
    show azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) = azim 0 v u w
    rw [iff1, c1, c2]
  -- u 项：ι(u)→v（iff，经 S3 径向零点 ⇒ 开锥成员）
  have hmem5 : ivsRhoNode1_p2 FF u ∈ affGt ({0, u} : Set V3) {v} :=
    (azim_eq_zero_iff hιu nCuv).mp hS3
  have iff5 : azim 0 u w v = azim 0 u w (ivsRhoNode1_p2 FF u) :=
    (azim_eq_azim_iff nCuw nCuv hιu).mpr hmem5
  have hupart : interiorAngle1_p2 0 FF u = azim 0 u w v := by
    show azim 0 u (rhoNode1_p2 FF u) (ivsRhoNode1_p2 FF u) = azim 0 u w v
    rw [hrho, iff5]
  -- w 项：ι(w)→u 精确（hivs），ρ(w)→v（compl 对，经 S4 径向零点 ⇒ 开锥成员）
  have hmem6 : v ∈ affGt ({0, w} : Set V3) {rhoNode1_p2 FF w} :=
    (azim_eq_zero_iff_alt hρw nCwv).mp hS4
  have iff6 : azim 0 w u (rhoNode1_p2 FF w) = azim 0 w u v :=
    (azim_eq_azim_iff nCwu hρw nCwv).mpr hmem6
  have c3 := azim_compl nCwu hρw
  have c4 := azim_compl nCwu nCwv
  rw [← iff6] at c4
  have hwpart : interiorAngle1_p2 0 FF w = azim 0 w v u := by
    show azim 0 w (rhoNode1_p2 FF w) (ivsRhoNode1_p2 FF w) = azim 0 w v u
    rw [hivs, c3, c4]
  exact ⟨hvpart, hupart, hwpart⟩

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k6_azim_zero_of_affGe
#print axioms Kepler.Text.pW6k6_coplanar_of_azim_pi
#print axioms Kepler.Text.pW6k6_azim_zero_of_affGe
#print axioms Kepler.Text.pW6k6_iter_ivs
#print axioms Kepler.Text.pW6k6_identification

/-
Kepler/Text/LocalFanStepW6K5.lean — wave C-W6-K5（步骤 ④）：else 支收口链。

HOL 对照（NKEZBFC.hl:2039-2614 末段）：B 支坍缩后 else 支（三点内角全 < π）
不导 False，而是直接证 `0 ≤ sol_local`：AZIM_DIVH + VOLUME_SOLID_TRIANGLE
给 `ΣdihV ≥ π`（Lean 侧即 pW6k4 的 ③ 闭合件），AZIM_DIVH 同案（`azim < π`）
给 `dihV = azim = int`，故 `solLocal = 2π + Σ(int−π) = ΣdihV − π ≥ 0`。

件目：
* §1 `pW6k5_coplanar_insert`：共线三点 + 任第四点 ⇒ 共面（插入桥）。
* §2 `pW6k5_notCollinear3_0_of_notCoplanar4` / `pW6k5_ne_of_notCoplanar4` /
  `pW6k5_notCoplanar_congr`：¬Coplanar 四点组的推论（含 0 三点不共线 /
  两点互异 / 集合排列迁移）。
* §3 `pW6k5_setSum_three`：三点集 setSum 求值（pW2_setSum_insert 模式）。
* §4 `pW6k5_sol_nonneg_of_azim_id`：④ 主件——azim↔int 识别式与三点全 < π
  作为显式前提（fan 语境的识别式推导 = azim 加和桥 + 望远镜，下一波），
  链 = collapse + azim_dihv_same ×3 + pW6k4_dihV_sum_ge_pi。
-/
import Kepler.Text.LocalFanStepW6K4
import Kepler.Text.LocalFanStepBW2

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 共线⇒共面插入桥 -/

/-- `Collinear3 a b c` 加任第四点仍共面（`Coplanar` 定义直推）。 -/
theorem pW6k5_coplanar_insert {a b c d : V3} (hcol : Collinear3 a b c) :
    Coplanar ({a, b, c, d} : Set V3) := by
  rw [Collinear3, collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨p₀, t, ht⟩ := hcol
  refine ⟨p₀, p₀ + t, d, fun q hq => ?_⟩
  have hsub : ({p₀, p₀ + t} : Set V3) ⊆ ({p₀, p₀ + t, d} : Set V3) := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ⊢
    tauto
  have hline : ∀ r ∈ ({a, b, c} : Set V3),
      r ∈ (affineSpan ℝ ({p₀, p₀ + t} : Set V3) : Set V3) := by
    intro r hr
    obtain ⟨s, hs⟩ := ht r hr
    have hvsub : (p₀ + t) -ᵥ p₀ = t := by
      simp only [vsub_eq_sub]
      abel
    have hls : s • t +ᵥ p₀ = AffineMap.lineMap p₀ (p₀ + t) s := by
      rw [AffineMap.lineMap_apply, hvsub]
    rw [hs, hls]
    exact AffineMap.lineMap_mem_affineSpan_pair s p₀ (p₀ + t)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with hqa | hqb | hqc | hqd
  · rw [hqa]
    exact affineSpan_mono ℝ hsub (hline a (by simp))
  · rw [hqb]
    exact affineSpan_mono ℝ hsub (hline b (by simp))
  · rw [hqc]
    exact affineSpan_mono ℝ hsub (hline c (by simp))
  · rw [hqd]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))

/-! ## §2 ¬Coplanar 四点组的推论 -/

/-- 四点组 `{0,x,y,z}` 不共面 ⇒ 含 0 的三点不共线。 -/
theorem pW6k5_notCollinear3_0_of_notCoplanar4 {x y z : V3}
    (hcop : ¬ Coplanar ({0, x, y, z} : Set V3)) : ¬ Collinear3 (0 : V3) x y :=
  fun hc => hcop (pW6k5_coplanar_insert hc)

/-- 四点组 `{0,x,y,z}` 不共面 ⇒ 前两点互异。 -/
theorem pW6k5_ne_of_notCoplanar4 {x y z : V3}
    (hcop : ¬ Coplanar ({0, x, y, z} : Set V3)) : x ≠ y := by
  intro h
  apply hcop
  have hset : ({0, x, y, z} : Set V3) = ({0, y, z} : Set V3) := by
    rw [h]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact coplanar_triple 0 y z

/-- 四点组不共面性按集合相等迁移。 -/
theorem pW6k5_notCoplanar_congr {p q r x y z : V3}
    (heq : ({0, p, q, r} : Set V3) = ({0, x, y, z} : Set V3))
    (hcop : ¬ Coplanar ({0, x, y, z} : Set V3)) :
    ¬ Coplanar ({0, p, q, r} : Set V3) :=
  fun h => hcop (heq ▸ h)

/-! ## ## §3 三点集 setSum 求值 -/

private theorem pW6k5_setSum_three {x y z : V3} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (f : V3 → ℝ) :
    setSum ({x, y, z} : Set V3) f = f x + f y + f z := by
  have hfin : ({y, z} : Set V3).Finite := (Set.finite_singleton z).insert y
  have hy : y ∉ ({z} : Set V3) := by simp [hyz]
  have hx : x ∉ ({y, z} : Set V3) := by simp [hxy, hxz]
  simp only [setSum, dif_pos (hfin.insert x),
    Set.Finite.toFinset_insert (hfin.insert x), Set.Finite.toFinset_insert hfin,
    Set.Finite.toFinset_singleton, add_assoc]
  rw [Finset.sum_insert (by simpa using hx), Finset.sum_insert (by simpa using hy),
    Finset.sum_singleton]

/-! ## ## §4 ④ 主件：else 支 solLocal ≥ 0 -/

/-- **W6-K5 ④**：collapse 后三点 `{v,u,w}` 不共面、azim↔int 识别式成立、
三点内角全 `< π` ⇒ `0 ≤ solLocal_p9 E FF`
（识别式与 `i`、telescope 相关前提由总装波提供，本件显式槽化）。 -/
theorem pW6k5_sol_nonneg_of_azim_id
    (hcl : convexLocalFan_p2 V E FF)
    {v u w : V3}
    (hcollapse : setSum V (fun x => interiorAngle1_p2 0 FF x - Real.pi)
      = setSum ({v, u, w} : Set V3)
        (fun x => interiorAngle1_p2 0 FF x - Real.pi))
    (hcop : ¬ Coplanar ({0, v, u, w} : Set V3))
    (haid : azim 0 v u w = interiorAngle1_p2 0 FF v
      ∧ azim 0 u w v = interiorAngle1_p2 0 FF u
      ∧ azim 0 w v u = interiorAngle1_p2 0 FF w)
    (hlt : interiorAngle1_p2 0 FF v < Real.pi
      ∧ interiorAngle1_p2 0 FF u < Real.pi
      ∧ interiorAngle1_p2 0 FF w < Real.pi) :
    0 ≤ solLocal_p9 E FF := by
  have heq1 : ({0, u, w, v} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have heq2 : ({0, v, w, u} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have heq3 : ({0, u, v, w} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have heq4 : ({0, w, v, u} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have heq5 : ({0, w, u, v} : Set V3) = ({0, v, u, w} : Set V3) := by
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hvu : v ≠ u := pW6k5_ne_of_notCoplanar4 hcop
  have huw : u ≠ w := pW6k5_ne_of_notCoplanar4 (pW6k5_notCoplanar_congr heq1 hcop)
  have hvw : v ≠ w := pW6k5_ne_of_notCoplanar4 (pW6k5_notCoplanar_congr heq2 hcop)
  have hav1 : azim 0 v u w < Real.pi := by rw [haid.1]; exact hlt.1
  have hav2 : azim 0 u w v < Real.pi := by rw [haid.2.1]; exact hlt.2.1
  have hav3 : azim 0 w v u < Real.pi := by rw [haid.2.2]; exact hlt.2.2
  have hπ := pW6k4_dihV_sum_ge_pi hcop
  have d1 : dihV 0 v u w = interiorAngle1_p2 0 FF v := by
    rw [← haid.1]
    exact (azim_dihv_same (pW6k5_notCollinear3_0_of_notCoplanar4 hcop)
      (pW6k5_notCollinear3_0_of_notCoplanar4
        (pW6k5_notCoplanar_congr heq2 hcop)) hav1).symm
  have d2 : dihV 0 u w v = interiorAngle1_p2 0 FF u := by
    rw [← haid.2.1]
    exact (azim_dihv_same (pW6k5_notCollinear3_0_of_notCoplanar4
        (pW6k5_notCoplanar_congr heq1 hcop))
      (pW6k5_notCollinear3_0_of_notCoplanar4
        (pW6k5_notCoplanar_congr heq3 hcop)) hav2).symm
  have d3 : dihV 0 w v u = interiorAngle1_p2 0 FF w := by
    rw [← haid.2.2]
    exact (azim_dihv_same (pW6k5_notCollinear3_0_of_notCoplanar4
        (pW6k5_notCoplanar_congr heq4 hcop))
      (pW6k5_notCollinear3_0_of_notCoplanar4
        (pW6k5_notCoplanar_congr heq5 hcop)) hav3).symm
  have hsum := pW6k5_setSum_three hvu hvw huw
    (fun x => interiorAngle1_p2 0 FF x - Real.pi)
  rw [SOL_LOFA_EQ_SUM_INANGLE_p9 hcl, hcollapse, hsum]
  show 0 ≤ 2 * Real.pi + ((interiorAngle1_p2 0 FF v - Real.pi) +
    (interiorAngle1_p2 0 FF u - Real.pi) + (interiorAngle1_p2 0 FF w - Real.pi))
  rw [← d1, ← d2, ← d3]
  linarith

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k5_coplanar_insert
#print axioms Kepler.Text.pW6k5_coplanar_insert
#print axioms Kepler.Text.pW6k5_sol_nonneg_of_azim_id

import Kepler.Text.PackingAuto2

/-!
# SF 项 15（KSOQKWL）反例机器验证 —— /tmp 探针（零 tracked 文件改动）

命题（docs/statement-fix-proposals.md `## 19'.(b)`，PA7 `KSOQKWL` = Rogers.hl:9588）：
Lean 侧 `permutes p (Set.Icc 0 k)` 是集合稳定弱编码（缺 HOL `permutes`
（permutations.ml:9）的补集逐点固定支 `!x. ¬(x IN s) ==> p x = x`），
该弱编码下 KSOQKWL 为假。

反例（k = 0 路线，全前提机器验证）：
- `k := 0`，`ul := [0]`，`V := {0}`，`p := Equiv.swap 1 2`。
- 几何半边：
  - `Packing {0}`：单点平凡；
  - `barV {0} 0 [0]`：唯一正长初始子列是 `[0]` 本身；其 voronoi 胞
    `voronoiList {0} [0] = voronoiClosed {0} 0 = univ`（V 只含 0，胞内
    自比较恒真），故 `affDim = finrank (vectorSpan univ) = finrank ⊤ = 3`；
  - `hl [0] = radV {0} = 0 < √2`（单点集外接半径为 0）。
- 结构半边：
  - `permutes (swap 1 2) (Icc 0 0)`：0 被固定，集合稳定成立；
  - `leftActionList (swap 1 2) [0] = [0]`（`p.symm 0 = 0`，PA2:159 定义），
    故 `rogers V ul = rogers V (leftActionList p ul)` 平凡真；
  - 但 `p ≠ Equiv.refl`（`p 1 = 2 ≠ 1`）。
- 补集不固定：`¬ ∀ x > 0, p x = x`（x = 1 处 `p 1 = 2`）——恰为补丁 15
  新增前提 `hpout` 所排除的对象（HOL 原文下该 p 不满足 permutes）。

几何实例化选点说明：提案 19'.(b) 草案建议 V := {0, 2e₁, 2e₂, 2e₃}（需
voronoi 胞 affDim=3 计算）；本探针取更省的合法实例 V := {0}（单点 packing），
k = 0 时 barV 的初始子列条件只含 `[0]` 一项，胞 = univ 使 affDim=3 平凡。
结论不受影响：反例只需要存在一个满足全部弱前提的四元组。
-/

namespace SF15Probe

open Kepler Kepler.Geom Kepler.Text Set Classical

/-! ### 几何半边 helpers -/

/-- `voronoi_list` of a singleton is the cell（PA14 私件 `p14_voronoiList_sing`
同法：rw 展开 + ext + simp [setOfList]）。 -/
private theorem sf15_voronoiList_sing (V : Set V3) (u : V3) :
    voronoiList V [u] = voronoiClosed V u := by
  rw [voronoiList, voronoiSet]
  ext x
  simp [setOfList]

/-- 单点 packing 的 voronoi 胞是全空间（V = {0}：与唯一成员自比较恒真）。 -/
private theorem sf15_cell_univ : voronoiClosed ({0} : Set V3) 0 = (Set.univ : Set V3) := by
  apply Set.eq_univ_of_forall
  intro x
  show ∀ w ∈ ({0} : Set V3), dist x 0 ≤ dist x w
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]

/-- 全空间的 vectorSpan 是 ⊤（PA14 私件 `p14_affDim_voronoiClosed` 的
basisFun 张成骨架，去掉 packing 侧条件后的平凡版）。 -/
private theorem sf15_vectorSpan_univ : vectorSpan ℝ (Set.univ : Set V3) = ⊤ := by
  have h1 : (⊤ : Submodule ℝ V3) ≤ vectorSpan ℝ (Set.univ : Set V3) := by
    rw [vectorSpan_def, ← (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.span_eq]
    refine Submodule.span_le.2 ?_
    rintro e ⟨i, rfl⟩
    refine Submodule.subset_span ?_
    refine Set.mem_vsub.2 ?_
    refine ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i, Set.mem_univ _, 0, Set.mem_univ _,
      by simp [vsub_eq_sub]⟩
  exact le_antisymm le_top h1

/-- affDim (voronoi 胞) = 3（PA14:399-402 同款收尾）。 -/
private theorem sf15_affDim : affDim (voronoiList ({0} : Set V3) [0]) = 3 := by
  have hv : vectorSpan ℝ (voronoiList ({0} : Set V3) [0]) = ⊤ := by
    rw [sf15_voronoiList_sing, sf15_cell_univ]
    exact sf15_vectorSpan_univ
  have hne : (voronoiList ({0} : Set V3) [0]).Nonempty :=
    ⟨0, by rw [sf15_voronoiList_sing, sf15_cell_univ]; trivial⟩
  simp only [affDim, if_neg (nonempty_iff_ne_empty.1 hne)]
  rw [hv, finrank_top]
  norm_cast
  exact finrank_euclideanSpace_fin

/-- `voronoiNondg {0} [0]`（barV V 0 的唯一实质初始子列条件）。 -/
private theorem sf15_voronoiNondg : voronoiNondg ({0} : Set V3) [0] := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro x hx
    simpa [setOfList] using hx
  · show affDim (voronoiList ({0} : Set V3) [0]) + ((1 : ℕ) : ℤ) = 4
    rw [sf15_affDim]
    norm_num

/-- `barV {0} 0 [0]`（PA2 私件 `p2g_barV_0` 骨架；初始子列分类 + 上条）。 -/
private theorem sf15_barV : barV ({0} : Set V3) 0 [0] := by
  refine ⟨by norm_num, ?_⟩
  rintro vl ⟨⟨yl, heq⟩, hpos⟩
  have hlen : vl.length + yl.length = 1 := by
    rw [← List.length_append, ← heq]; norm_num
  have hyl : yl = [] := List.length_eq_zero_iff.mp (by omega)
  rw [hyl, List.append_nil] at heq
  subst heq
  exact sf15_voronoiNondg

/-- 单点集是 packing。 -/
private theorem sf15_packing : Packing ({0} : Set V3) := by
  intro u hu v hv _
  rw [Set.mem_singleton_iff.mp hu, Set.mem_singleton_iff.mp hv]

/-- 单点集 circumcenter（PA2 私件 `p3a_CC_SING` 逐字副本，探针自用）。 -/
private theorem sf15_circumcenter_sing (u : V3) : circumcenter ({u} : Set V3) = u := by
  have hspec := Classical.epsilon_spec
    (p := fun v : V3 => v ∈ (affineSpan ℝ ({u} : Set V3) : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({u} : Set V3), c = dist v w)
    ⟨u, (AffineSubspace.mem_affineSpan_singleton ℝ V3).2 rfl, 0, by simp⟩
  exact (AffineSubspace.mem_affineSpan_singleton ℝ V3).mp (SetLike.mem_coe.mpr hspec.1)

/-- 单点集 circumradius = 0（epsilon 谓词子单点性）。 -/
private theorem sf15_radV_sing (u : V3) : radV ({u} : Set V3) = 0 := by
  have hspec2 := Classical.epsilon_spec
    (p := fun c : ℝ => ∀ w ∈ ({u} : Set V3), c = dist (circumcenter ({u} : Set V3)) w)
    ⟨0, by
      intro w hw
      rw [Set.mem_singleton_iff.mp hw, sf15_circumcenter_sing]
      simp⟩
  trans dist (circumcenter ({u} : Set V3)) u
  · exact hspec2 u (Set.mem_singleton_iff.mpr rfl)
  · rw [sf15_circumcenter_sing]
    simp

/-- `hl [0] = 0 < √2`。 -/
private theorem sf15_hl : hl ([0] : List V3) < Real.sqrt 2 := by
  have hset : setOfList ([0] : List V3) = ({0} : Set V3) := by ext z; simp [setOfList]
  show radV (setOfList [0]) < Real.sqrt 2
  rw [hset, sf15_radV_sing]
  exact Real.sqrt_pos.mpr (by norm_num)

/-! ### 反例见证与两推论 -/

/-- 反例见证：弱编码 KSOQKWL 的全部前提 + 结论否定同时可满足。 -/
theorem sf15_counterexample_witness :
    ∃ (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ),
      Packing V ∧ barV V k ul ∧ hl ul < Real.sqrt 2 ∧ permutes p (Set.Icc 0 k) ∧
        rogers V ul = rogers V (leftActionList p ul) ∧ p ≠ _root_.Equiv.refl ℕ := by
  -- 结构半边
  have hp0 : Equiv.swap 1 2 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)
  have hs0 : (Equiv.swap 1 2).symm 0 = 0 :=
    (Equiv.symm_apply_eq (Equiv.swap 1 2)).2 hp0
  have hmem0 : ∀ y : ℕ, y ∈ Set.Icc 0 0 ↔ y = 0 := by
    intro y
    simp only [Set.mem_Icc]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => by rw [h]; exact ⟨le_refl 0, le_refl 0⟩⟩
  have hperm : permutes (Equiv.swap 1 2) (Set.Icc 0 0) := by
    intro x
    rw [hmem0 x, hmem0 (Equiv.swap 1 2 x)]
    constructor
    · intro hx; rw [hx, hp0]
    · intro hx
      have hstep : x = (Equiv.swap 1 2).symm (Equiv.swap 1 2 x) :=
        (Equiv.apply_symm_apply (Equiv.swap 1 2) x).symm
      calc x = (Equiv.swap 1 2).symm (Equiv.swap 1 2 x) := hstep
        _ = (Equiv.swap 1 2).symm 0 := by rw [hx]
        _ = 0 := hs0
  have hla : leftActionList (Equiv.swap 1 2) ([0] : List V3) = [0] := by
    rfl
  refine ⟨({0} : Set V3), [0], Equiv.swap 1 2, 0, sf15_packing, sf15_barV, sf15_hl, hperm,
    congrArg (rogers ({0} : Set V3)) hla, ?_⟩
  intro h
  have h1 := Equiv.ext_iff.mp h 1
  rw [Equiv.swap_apply_left] at h1
  simp only [Equiv.refl_apply] at h1
  omega

/-- KSOQKWL 弱编码陈述（PA7:2197 去掉补丁 15 的 `hpout` 后的原文形状）为假。 -/
theorem sf15_KSOQKWL_weak_false :
    ¬ ∀ (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ),
        Packing V → barV V k ul → hl ul < Real.sqrt 2 →
          permutes p (Set.Icc 0 k) →
          rogers V ul = rogers V (leftActionList p ul) → p = _root_.Equiv.refl ℕ := by
  intro H
  obtain ⟨V, ul, p, k, hP, hb, hhl, hperm, hrog, hpne⟩ := sf15_counterexample_witness
  exact hpne (H V ul p k hP hb hhl hperm hrog)

/-- 补丁 15 的 `hpout` 前提恰好排除本反例（k = 0 < 1 = k+1 处 p 移动了 1）。 -/
theorem sf15_hpout_blocks :
    ¬ (∀ x : ℕ, 0 < x → (Equiv.swap 1 2 : Equiv.Perm ℕ) x = x) := by
  intro H
  have h1 := H 1 (by norm_num)
  rw [Equiv.swap_apply_left] at h1
  omega

#print axioms sf15_KSOQKWL_weak_false
#print axioms sf15_counterexample_witness
#print axioms sf15_hpout_blocks

end SF15Probe

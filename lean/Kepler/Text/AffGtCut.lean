/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 19:
skeleton pass of `AFF_GT_CUT_XFAN_IMP_EDGE_FAN` (planarity.hl:7788-8998).

Source: `scripts/planarity.hl` (persistent copy of Flyspeck book
formalization `reference/flyspeck/text_formalization/fan/planarity.hl`,
Hoang Le Truong, 2010).

This file is the skeleton of the 1,211-line HOL monolith. The main
theorem's setup and the case-tree assembly are fully proved; the nine
branch lemmas below carry `by sorry` and are to be filled in later
slices (branch `wip/aff-gt-cut` allows marked sorries; `main` does not).

HOL macro structure of :7788-8998 (all line numbers below refer to
planarity.hl):

* Setup (:7801-7860): from `~(aff_gt {x} {v,w} INTER xfan = {})` take a
  witness `x'` with `x' IN aff_gt {x} {v,w}` and `x' IN aff_ge {x} e`,
  `e IN E`; `expand_edge_graph_fan` writes `e = {v', w'}`; extract
  coefficient tuples `(t1,t2,t3)` (from `AFF_GT_1_2`) and
  `(t1',t2',t3')` (from `AFF_GE_1_2`).
* Main case split on `t3' = 0` (:7840):
  - `t3' = 0, t2' = 0` (:7847-7888): `x' IN aff {x}` forces
    `w IN aff {x,v}`, contradicting `~collinear {x,v,w}`. [S1]
  - `t3' = 0, t2' > 0` (:7890-8013): solve `v' IN aff_gt {x} {v,w}`
    [S2], transfer non-coplanarity `{x,v,u,w} -> {x,v',v,u}` [S3],
    `exists_element_in_half_sapace_fan` gives `u'`, then the shared
    cut/contradiction tail [S7] (exists_cut_small_edges_fan_le +
    not_cut_in_edges_fan).
  - `t3' > 0, t2' = 0` (:8015-8153): mirror with `w'` for `v'`.
  - `t3' > 0, t2' > 0` (:8155-8998), the generic branch: memberships
    (:8156-8201, inline), four non-collinearity facts
    `~collinear {x,x',w'}`, `~collinear {x,x',v'}`, `~collinear
    {x,x',w}`, `~collinear {x,x',v}` (:8202-8330) [S4-S6], then azim
    trichotomy on `azim x x' v w'` (:8330):
    + `0 < azim < pi` (:8331-8352): cut/contradiction tail with
      `p = x'`, `q = w'` [S7, inline assembly].
    + `pi < azim` (:8353-8438): `aff_gt2_subset_aff_ge` +
      `sum5_azim_fan` give `0 < azim x x' v v' < pi`; tail with
      `q = v'` [S7, inline assembly].
    + `azim = 0` (:8388-8712): if `w'` or `v'` lies in
      `aff_gt {x} {v,w}` (:8391-8541) use [S3] + tail [S7]; otherwise
      the fan7 analysis (:8542-8712) closes via
      `decomposition_planar_by_angle_fan` + `properties_of_fan7` /
      `properties1_of_fan7`, concluding `{v,w} IN E` exactly when
      `{v,w} = {v',w'}` as unordered pairs [S8].
    + `azim = pi` (:8714-8998): `sum5_azim_fan` reduces to
      `azim x x' v v' = 0`, then the azim = 0 branch with `v'`/`w'`
      swapped [S9 delegates to S8].

Slice list (lemma -> HOL lines -> difficulty):
* S1 `absurd_degenerate_x'`  :7847-7888    liangou (coefficient shuffle)
* S2 `mem_affGt_of_eq`       :7890-7903,   liangou (solve for p,
  7966-7976, 8097-8114                     `remove_variable_fan` style)
* S3 `coplanar_transfer`     :7897-7965 +   fenxi (HOL uses translation
  5 mirrors (8026-8096, 8391-8435,          + scaling of coplanarity;
  8466-8510, 8727-8771, 8806-8850)          Lean: affineSpan witnesses)
* S4 `nc3_x'_of_combo`       :8202-8255     liangou
* S5 `nc3_x'_w`              :8256-8291     liangou
* S6 `nc3_x'_v`              :8292-8330     liangou
* S7 `cut_contra`            :7970-8013,    zuzhuang (three public
  8114-8153, 8331-8352, 8354-8438 +         lemmas + set algebra; six
  the tails of :8391-8541, :8727-8884       HOL occurrences)
* S8 `final_neither_azim0`   :8542-8712      fenxi+zuzhuang (hardest;
  incl. prologue :8377-8388                  fan7 / decomposition web)
* S9 `final_azim_pi`         :8714-8998      zuzhuang (reduces to S8
                                              with v'/w' swapped)

Difficulty scale: liangou = coefficient/rewriting bookkeeping;
fenxi = geometric content (coplanarity/azim half-space arguments);
zuzhuang = assembly of already-ported public lemmas.

Conventions: HOL line numbers in the head comment of each item;
`sorry` only in the nine marked slices; `lake env lean` reports zero
errors (only "declaration uses 'sorry'" warnings).
-/
import Kepler.Text.PlanarityNotCut

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

variable {x v u w : V3} {V : Set V3} {E : Set (Set V3)}

/-! ## 小工具（真证明） -/

/-- `Collinear3` 后两点交换（两处文件内私有镜像的本地副本）。 -/
private theorem coll3_swap' {x p q : V3} (h : Collinear3 x p q) : Collinear3 x q p := by
  have hset : ({x, q, p} : Set V3) = ({x, p, q} : Set V3) := by ext a; simp; tauto
  show Collinear ℝ ({x, q, p} : Set V3)
  rw [hset]
  exact h

/-- 非共线给出 `Disjoint {x} {p,q}`（`PlanarityNotCut` 私有引理的本地镜像）。 -/
private theorem disjoint_of_nc3 {x p q : V3} (hnc : ¬ Collinear3 x p q) :
    Disjoint ({x} : Set V3) {p, q} := by
  rw [Set.disjoint_singleton_left]
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact hnc (collinear3_of_eq (v := x) (w := p) (w1 := q) h.symm)
  · exact hnc (collinear3_pair_left (v0 := x) (v1 := p) (x := q) h.symm)

/-- 集合二元文字的交换（本文件多处需要的局部事实）。 -/
private theorem pair_comm_set (a b : V3) : ({a, b} : Set V3) = ({b, a} : Set V3) := by
  ext z; simp; tauto

/-- 三点（`x,p,v`）仿射组合落入仿射子空间：`c1•x + c2•p + c3•v`
（系数和 1）仍在该子空间内（S3 中 `w ∈ P` 的载体，vadd/direction 闭包）。 -/
private theorem mem_affineSpan_comb {S : AffineSubspace ℝ V3} {x p v y : V3} {c1 c2 c3 : ℝ}
    (hx : x ∈ (S : Set V3)) (hp : p ∈ (S : Set V3)) (hv : v ∈ (S : Set V3))
    (hsum : c1 + c2 + c3 = 1) (hy : y = c1 • x + c2 • p + c3 • v) :
    y ∈ (S : Set V3) := by
  have hd2 : c2 • (p - x) ∈ S.direction :=
    Submodule.smul_mem _ c2 (AffineSubspace.vsub_mem_direction hp hx)
  have hd3 : c3 • (v - x) ∈ S.direction :=
    Submodule.smul_mem _ c3 (AffineSubspace.vsub_mem_direction hv hx)
  have hval : y = (c2 • (p - x) + c3 • (v - x)) +ᵥ x := by
    rw [hy, vadd_eq_add]
    calc
      c1 • x + c2 • p + c3 • v = x + c2 • (p - x) + c3 • (v - x) := by
        rw [show c1 = 1 - c2 - c3 by linarith]
        module
      _ = (c2 • (p - x) + c3 • (v - x)) + x := by
        abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.add_mem _ hd2 hd3) hx

/-- 消元辅助（S4-S6 共用）：`y` 与 `x,r` 共线且 `y = c1•x + c2•q + c3•r`
（`c2 ≠ 0`，系数和 1）时 `q ∈ aff {x,r}`（两点表示后除以 `c2`）。 -/
private theorem mem_affLine_of_collinear3 {x q r y : V3} {c1 c2 c3 : ℝ}
    (hxr : x ≠ r) (hcol : Collinear3 x y r) (hc2 : c2 ≠ 0)
    (hsum : c1 + c2 + c3 = 1) (hyeq : y = c1 • x + c2 • q + c3 • r) :
    q ∈ (affineSpan ℝ ({x, r} : Set V3) : Set V3) := by
  have hcol' : y ∈ (affineSpan ℝ ({x, r} : Set V3) : Set V3) :=
    (collinear3_iff_mem_affineSpan (v0 := x) (v1 := r) (y := y) hxr).mp
      (coll3_swap' hcol)
  rw [affine_hull_2_fan] at hcol'
  obtain ⟨t1, t2, htsum, hyt⟩ := hcol'
  have hkey : c2 • q = (t1 - c1) • x + (t2 - c3) • r := by
    have e : c1 • x + c2 • q + c3 • r = t1 • x + t2 • r := by
      rw [← hyeq, hyt]
    calc
      c2 • q = t1 • x + t2 • r - (c1 • x + c3 • r) := by
        rw [← e]
        module
      _ = (t1 - c1) • x + (t2 - c3) • r := by
        module
  have hq : q = ((t1 - c1) / c2) • x + ((t2 - c3) / c2) • r := by
    rw [← inv_smul_smul₀ hc2 q, hkey, smul_add, smul_smul, smul_smul]
    module
  rw [affine_hull_2_fan]
  refine ⟨_, _, ?_, hq⟩
  field_simp
  linarith

/-! ## S1：退化情形 `t3' = t2' = 0`（HOL :7847-7888） -/

/-- HOL :7847-7888（`t3' = 0 /\ t2' = 0` 支）：`y = s1 • x` 且
`y = t1 • x + t2 • v + t3 • w`（`t3 > 0`，系数和 1，`s1 = 1`）联立得
`t3 • (w - x) = -(t2) • (v - x)`，故 `w = (1 + t2/t3) • x - (t2/t3) • v
∈ aff {x, v}`，与 `¬Collinear3 x v w` 矛盾。只需 `t3 ≠ 0`；
模板：`remove_variable_fan`（Planarity.lean）的消元 + 
`collinear3_iff_mem_affineSpan`。难度：良构。 -/
private theorem absurd_degenerate_x' {x v w y : V3} {s1 t1 t2 t3 : ℝ} (hs1 : s1 = 1)
    (hyx : y = s1 • x) (hyvw : y = t1 • x + t2 • v + t3 • w)
    (ht3 : 0 < t3) (htsum : t1 + t2 + t3 = 1)
    (hnc : ¬ Collinear3 x v w) : False := by
  have ht3ne : t3 ≠ 0 := ne_of_gt ht3
  have hxv : x ≠ v := by
    intro he
    apply hnc
    exact collinear3_of_eq (v := x) (w := v) (w1 := w) he.symm
  have hyx' : y = x := by
    rw [hs1, one_smul] at hyx
    exact hyx
  -- 联立两组表达：t1•x + t2•v + t3•w = x
  have h1 : t1 • x + t2 • v + t3 • w = x := by
    rw [hyx'] at hyvw
    exact hyvw.symm
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  rw [ht1] at h1
  have hz : (1 - t2 - t3) • x + t2 • v + t3 • w - x = 0 := sub_eq_zero.mpr h1
  have hexp : (1 - t2 - t3) • x + t2 • v + t3 • w - x =
      t2 • (v - x) + t3 • (w - x) := by
    module
  rw [hexp] at hz
  -- 解出 w - x = (-(t2 / t3)) • (v - x)，故 w ∈ aff {x, v}
  have hd : w - x = (-(t2 / t3)) • (v - x) := by
    have h2 : t3⁻¹ • (t2 • (v - x) + t3 • (w - x)) = (0 : V3) := by
      rw [hz, smul_zero]
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht3ne, one_smul] at h2
    rw [show t3⁻¹ * t2 = t2 / t3 from by field_simp] at h2
    have h3 : w - x = -((t2 / t3) • (v - x)) :=
      (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h2))
    rw [h3, neg_smul]
  have hwspan : w ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨-(t2 / t3), ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hd]
    module
  exact hnc ((collinear3_iff_mem_affineSpan hxv).mpr hwspan)

/-! ## S2：从两组系数解出端点落在 `affGt {x} {v,w}`（HOL :7890-7903,
:7966-7976 与镜像 :8097-8114） -/

/-- HOL :7966-7976（SUBGOAL 4，及其在 :8097-8114 的 `w'` 镜像）：
`y = s1 • x + s2 • p`（`s2 > 0`，`s1 + s2 = 1`）且
`y = t1 • x + t2 • v + t3 • w`（`t2, t3 > 0`，和 1）时，消去 `y` 得
`p = (1 - s2⁻¹ * t2 - s2⁻¹ * t3) • x + (s2⁻¹ * t2) • v + (s2⁻¹ * t3) • w`，
后两系数严格正，故 `p ∈ affGt {x} {v,w}`（`aff_gt_1_2`）。难度：良构。 -/
private theorem mem_affGt_of_eq {x v w p : V3} {y : V3} {s1 s2 t1 t2 t3 : ℝ}
    (hdis : Disjoint ({x} : Set V3) {v, w})
    (hs2 : 0 < s2) (hssum : s1 + s2 = 1)
    (hyp : y = s1 • x + s2 • p)
    (ht2 : 0 < t2) (ht3 : 0 < t3) (htsum : t1 + t2 + t3 = 1)
    (hyvw : y = t1 • x + t2 • v + t3 • w) :
    p ∈ affGt {x} {v, w} := by
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2
  have hy2 : s1 • x + s2 • p = t1 • x + t2 • v + t3 • w := by
    rw [← hyp]
    exact hyvw
  have hs2p : s2 • p = (t1 - s1) • x + t2 • v + t3 • w := by
    calc
      s2 • p = (t1 • x + t2 • v + t3 • w) - s1 • x := by
        rw [← hy2]
        module
      _ = (t1 - s1) • x + t2 • v + t3 • w := by
        module
  have hxcoef : s2⁻¹ * (t1 - s1) = 1 - s2⁻¹ * t2 - s2⁻¹ * t3 := by
    field_simp [hs2ne]
    linarith
  have hp : p = (1 - s2⁻¹ * t2 - s2⁻¹ * t3) • x + (s2⁻¹ * t2) • v +
      (s2⁻¹ * t3) • w := by
    have hp0 : p = s2⁻¹ • ((t1 - s1) • x + t2 • v + t3 • w) := by
      calc
        p = s2⁻¹ • (s2 • p) := by rw [inv_smul_smul₀ hs2ne]
        _ = s2⁻¹ • ((t1 - s1) • x + t2 • v + t3 • w) := by rw [hs2p]
    rw [hp0]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, hxcoef]
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq]
  refine ⟨1 - s2⁻¹ * t2 - s2⁻¹ * t3, s2⁻¹ * t2, s2⁻¹ * t3, ?_, ?_, ?_, hp⟩
  · exact mul_pos (inv_pos.mpr hs2) ht2
  · exact mul_pos (inv_pos.mpr hs2) ht3
  · ring

/-! ## S3：非共面性沿弦传递（HOL :7897-7965 及五处镜像） -/

/-- HOL :7897-7965（SUBGOAL 3）+ 镜像 :8026-8096、:8391-8435、
:8466-8510、:8727-8771、:8806-8850（共六处）：`p = a1 • x + a2 • v +
a3 • w`（`a3 > 0`，和 1）且 `¬Coplanar {x,v,u,w}` 时有
`¬Coplanar {x,p,v,u}`。HOL 走 COPLANAR_TRANSLATION_EQ +
continuous_coplanar_fan + COPLANAR_SCALE_ALL 的平移/缩放链；Lean 建议
重构：若 `{x,p,v,u}` 共面于平面 P，则 `w = a3⁻¹ • p - (a3⁻¹ * a1) • x -
(a3⁻¹ * a2) • v` 是 `{p,x,v}` 的仿射组合（系数和 `a3⁻¹ (1 - a1 - a2)
= 1`）故 `w ∈ P`，得 `Coplanar {x,v,u,w}` 矛盾。注意只需 `a3 ≠ 0`
（保留 `0 < a3` 以贴近 HOL 语义）。难度：分析（affineSpan 路线化后
偏良构）。 -/
private theorem coplanar_transfer {x v u w p : V3} {a1 a2 a3 : ℝ}
    (ha3 : 0 < a3) (hsum : a1 + a2 + a3 = 1)
    (hp : p = a1 • x + a2 • v + a3 • w)
    (hnc : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ¬ Coplanar ({x, p, v, u} : Set V3) := by
  have ha3ne : a3 ≠ 0 := ne_of_gt ha3
  intro hcop
  obtain ⟨a, b, c, hsub⟩ := hcop
  let S : AffineSubspace ℝ V3 := affineSpan ℝ ({a, b, c} : Set V3)
  have hx : x ∈ (S : Set V3) := hsub (by simp)
  have hpS : p ∈ (S : Set V3) := hsub (by simp)
  have hv : v ∈ (S : Set V3) := hsub (by simp)
  have hu : u ∈ (S : Set V3) := hsub (by simp)
  -- w = a3⁻¹ • p - (a3⁻¹*a1) • x - (a3⁻¹*a2) • v（解出 w，系数和 1）
  have hp3 : a3⁻¹ • p = (a3⁻¹ * a1) • x + (a3⁻¹ * a2) • v + w := by
    rw [hp]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    rw [show a3⁻¹ * a3 = 1 by rw [inv_mul_cancel₀ ha3ne]]
    rw [one_smul]
  have hw' : w = a3⁻¹ • p - (a3⁻¹ * a1) • x - (a3⁻¹ * a2) • v := by
    rw [hp3]
    abel
  have hw : w = (-(a3⁻¹ * a1)) • x + a3⁻¹ • p + (-(a3⁻¹ * a2)) • v := by
    calc
      w = a3⁻¹ • p - (a3⁻¹ * a1) • x - (a3⁻¹ * a2) • v := hw'
      _ = (-(a3⁻¹ * a1)) • x + a3⁻¹ • p + (-(a3⁻¹ * a2)) • v := by
        module
  have hsum' : -(a3⁻¹ * a1) + a3⁻¹ + -(a3⁻¹ * a2) = 1 := by
    field_simp [ha3ne]
    linarith
  have hwS : w ∈ (S : Set V3) := mem_affineSpan_comb hx hpS hv hsum' hw
  apply hnc
  refine ⟨a, b, c, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h1 | hz
  · rw [h1]
    exact hx
  rcases hz with h1 | hz
  · rw [h1]
    exact hv
  rcases hz with h1 | hz
  · rw [h1]
    exact hu
  · rw [hz]
    exact hwS

/-! ## S4-S6：一般情形的四条非共线（HOL :8202-8330） -/

/-- HOL :8202-8228（SUBGOAL 7）+ :8229-8255（SUBGOAL 8）：
`y = a1 • x + a2 • p + a3 • q`（`a2 > 0`，和 1）且 `¬Collinear3 x p q`
时 `¬Collinear3 x y q`。证：若 `y ∈ aff {x,q}`，联立两组系数解出
`p ∈ aff {x,q}`（`p = a2⁻¹ • y - (a2⁻¹ * a1) • x - (a2⁻¹ * a3) • q`，
系数和 1），与 `¬Collinear3 x p q` 矛盾。工具：`collinear3_iff_mem_
affineSpan` + `affine_hull_2_fan`。难度：良构。 -/
private theorem nc3_x'_of_combo {x p q y : V3} {a1 a2 a3 : ℝ}
    (ha2 : 0 < a2) (hsum : a1 + a2 + a3 = 1)
    (hyq : y = a1 • x + a2 • p + a3 • q)
    (hnc : ¬ Collinear3 x p q) : ¬ Collinear3 x y q := by
  have ha2ne : a2 ≠ 0 := ne_of_gt ha2
  have hxq : x ≠ q :=
    fun he => hnc (collinear3_pair_left (v0 := x) (v1 := p) (x := q) he.symm)
  intro hcol
  have hspan : p ∈ (affineSpan ℝ ({x, q} : Set V3) : Set V3) :=
    mem_affLine_of_collinear3 hxq hcol ha2ne hsum hyq
  exact hnc (coll3_swap' ((collinear3_iff_mem_affineSpan hxq).mpr hspan))

/-- HOL :8256-8291（SUBGOAL 9，`¬collinear {x,x',w}`）：`y = t1 • x +
t2 • v + t3 • w`（`t2 > 0`，和 1）且 `¬Collinear3 x v w` 时
`¬Collinear3 x y w`。证：若 `y ∈ aff {x,w}`（系数 `c1, c2`），联立得
`t2 • (v - x) = (c2 - t3) • (w - x)`，解出 `v` 为 `{x,w}` 的仿射组合
（系数和 1，含 `c2 = t3` 时 `v = x` 的退化子情形），与 `¬Collinear3
x v w` 矛盾。难度：良构。 -/
private theorem nc3_x'_w {x v w y : V3} {t1 t2 t3 : ℝ}
    (ht2 : 0 < t2) (hsum : t1 + t2 + t3 = 1)
    (hyeq : y = t1 • x + t2 • v + t3 • w)
    (hnc : ¬ Collinear3 x v w) : ¬ Collinear3 x y w := by
  have ht2ne : t2 ≠ 0 := ne_of_gt ht2
  have hxw : x ≠ w :=
    fun he => hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := w) he.symm)
  intro hcol
  have hspan : v ∈ (affineSpan ℝ ({x, w} : Set V3) : Set V3) :=
    mem_affLine_of_collinear3 hxw hcol ht2ne hsum hyeq
  exact hnc (coll3_swap' ((collinear3_iff_mem_affineSpan hxw).mpr hspan))

/-- HOL :8292-8330（SUBGOAL 10，`¬collinear {x,x',v}`）：同 `nc3_x'_w`
但解 `w`：若 `y ∈ aff {x,v}`，则 `t3 • w = (c1 - t1) • x + (c2 - t2) • v`
且系数和恰为 `t3`，解出 `w ∈ aff {x,v}` 矛盾。难度：良构。 -/
private theorem nc3_x'_v {x v w y : V3} {t1 t2 t3 : ℝ}
    (ht3 : 0 < t3) (hsum : t1 + t2 + t3 = 1)
    (hyeq : y = t1 • x + t2 • v + t3 • w)
    (hnc : ¬ Collinear3 x v w) : ¬ Collinear3 x y v := by
  have ht3ne : t3 ≠ 0 := ne_of_gt ht3
  have hxv : x ≠ v := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) he.symm)
  have hsum2 : t1 + t3 + t2 = 1 := by linarith
  have hy2 : y = t1 • x + t3 • w + t2 • v := by
    rw [hyeq]
    module
  intro hcol
  have hspan : w ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
    mem_affLine_of_collinear3 hxv hcol ht3ne hsum2 hy2
  exact hnc ((collinear3_iff_mem_affineSpan hxv).mpr hspan)

/-! ## S7：切割/矛盾共用尾段（HOL 六处） -/

/-- HOL :7970-8013（`t3'=0,t2'>0` 尾）、:8114-8153（`t2'=0` 镜像尾）、
:8331-8352（`0<azim<π` 支）、:8354-8438 尾（`π<azim` 支），以及
:8391-8541、:8727-8884 各支的收尾（共六处共用）：在
`p ∈ affGt {x} {v,w}`、`azim x p v q ∈ (0,π)`、`¬Collinear3 x p q` 且
`affGt {x} {p,q} ⊆ xfan` 时导出 False。证（三公开引理 + 集合代数）：
`exists_cut_small_edges_fan_le`（a := 1）给出 `t ∈ (0,1)` 与
`y ∈ affGt {x} {v,(1-t)•w+t•u} ∩ affGt {x} {p,q}`；`not_cut_in_edges_fan`
（a := 1-t）给出 `affGt {x} {v,(1-t)•w+t•u} ∩ xfan = ∅`；而
`y ∈ affGt {x} {p,q} ⊆ xfan`（hsub）。注意两处集合文字需用
`(1-1)•u+1•w = w` 与 `t•u+(1-t)•w = (1-t)•w+t•u` 归一。难度：组装。 -/
private theorem cut_contra {x v u w p q : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (h80 : fan80 x V E)
    (hnc : ¬ Collinear3 x p q)
    (hpgt : p ∈ affGt {x} {v, w})
    (h0 : 0 < azim x p v q) (hpi : azim x p v q < Real.pi)
    (hsub : affGt {x} {p, q} ⊆ xfan x V E) : False := by
  obtain ⟨t, ht0, ht1, hcut⟩ :=
    exists_cut_small_edges_fan_le (v1 := p) (u1 := q) (a := 1) hfan hvu huw hsigma
      (by norm_num) (by norm_num) h80 hnc (by simpa using hpgt) h0 hpi
  have hcut' : ¬(affGt {x} {v, (1 - t) • w + t • u} ∩ affGt {x} {p, q} = ∅) := by
    simpa using hcut
  have hempty : affGt {x} {v, (1 - t) • w + t • u} ∩ xfan x V E = ∅ := by
    have hne := not_cut_in_edges_fan (a := 1 - t) hfan hvu huw hsigma (by linarith)
      (by linarith) hcard h80
    have hvs : (1 - (1 - t)) • u + (1 - t) • w = (1 - t) • w + t • u := by
      module
    rw [hvs] at hne
    exact hne
  obtain ⟨y, hy⟩ :=
    (Set.nonempty_iff_ne_empty (s := affGt {x} {v, (1 - t) • w + t • u} ∩
      affGt {x} {p, q})).mpr hcut'
  have hy' : y ∈ affGt {x} {v, (1 - t) • w + t • u} ∧ y ∈ affGt {x} {p, q} := by
    simpa using hy
  exact (Set.eq_empty_iff_forall_notMem.mp hempty y) ⟨hy'.1, hsub hy'.2⟩

/-! ## S8：`azim x x' v w' = 0` 的双否半支（HOL :8542-8712） -/

/-- HOL :8542-8712（`azim x x' v w' = 0` 且 `w' ∉ affGt {x} {v,w}`、
`v' ∉ affGt {x} {v,w}` 的收尾；前奏 :8377-8388 的 AZIM_EQ_0 系列）：
结论 `{v,w} ∈ E`。结构（模板：`PlanarityNotCut.not_cut_inside_fan_
azim0`，假设即分支处全部局部事实）：
* :8542-8556 （15）：`¬(w' ∈ affGt {x} {x',v})`（`aff_gt3_subset_aff_gt`
  + `x' ∈ affGt {x} {v,w}`）。
* :8557-8610 （16a）：`azim_eq_zero_iff_alt` 给 `w' ∈ affGt {x,x'} {v}`
  → `affGt ⊆ affGe` → `decomposition_planar_by_angle_fan`：
  `v ∈ affGt {x} {x',w'}` 或 `w' ∈ affGe {x,x'} {v}`。
* 16a 前半：`aff_gt1_subset_aff_ge` 给 `v ∈ affGe {x} {v',w'}` →
  `properties_of_fan7` 给 `v = v' ∨ v = w'`；`v = v'` 时
  `aff_gt2_subset_aff_ge`（`azim x x' v' w' = π`）与 `h0` 改写后
  `0 = π` 矛盾（17a，:8565-8588）；`v = w'` 时再用
  `aff_ge1_subset_aff_ge` 链 + `properties_of_fan7 [w;u;v';w']` 得
  `w = v'`（此时 `{v,w} = {w',v'} ∈ E`，主目标达成，:8607）或
  `w = w'`（azim 冲突矛盾，:8608-8615 "XONG"）。
* 16b 后半（:8612-8712）：`aff_ge_subset_aff_gt_union_aff_ge` +
  `aff_gt_inter_aff_gt` 拆 `w' ∈ affGt {x,v} {x'} ∪ affGe {x} {v}`；
  `w' ∈ affGe {x} {v}` 走 `properties1_of_fan7`（`w' = v`）+
  `point_in_aff_ge` + `properties_of_fan7`，两 disjunct 均由
  `aff_gt2_subset_aff_ge` + `AZIM_EQ_PI_SYM`（azim_compl 推）+
  `sum4_azim_fan` + `AZIM_EQ_0_GE`（azim_eq_zero_iff + affGt⊆affGe）+
  `decomposition_planar_by_angle_fan` + `aff_gt1_subset_aff_gt` 的
  矛盾链关闭（17/18/19，:8676-8712）。难度：分析+组装（本文件最难片）。 -/
private theorem final_neither_azim0 {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    {x' v' w' : V3}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (he' : {v', w'} ∈ E)
    (hnc' : ¬ Collinear3 x v' w')
    (hx'gt : x' ∈ affGt {x} {v, w})
    (hx'gt' : x' ∈ affGt {x} {v', w'})
    (hx'ge' : x' ∈ affGe {x} {v', w'})
    (hncw' : ¬ Collinear3 x x' w') (hncv' : ¬ Collinear3 x x' v')
    (hncw : ¬ Collinear3 x x' w) (hncv : ¬ Collinear3 x x' v)
    (h0 : azim x x' v w' = 0)
    (hnw' : ¬ (w' ∈ affGt {x} {v, w})) (hnv' : ¬ (v' ∈ affGt {x} {v, w})) :
    {v, w} ∈ E := by
  sorry

/-! ## S9：`azim x x' v w' = π` 支（HOL :8714-8998） -/

/-- HOL :8714-8998（`azim x x' v w' = π` 支；模板：
`PlanarityNotCut.not_cut_inside_fan_azim_pi`）：先做 CUOI 归约
（:8714-8721）：`aff_gt2_subset_aff_ge` 给 `azim x x' v' w' = π`，
`sum5_azim_fan` 与 hπ 联立得 `azim x x' v v' = 0`；随后 `w' ∈
affGt {x} {v,w}`（:8727-8805）与 `v' ∈ affGt {x} {v,w}`（:8806-8884）
两半支各由 `coplanar_transfer` + `exists_element_in_half_sapace_fan`
+ `cut_contra` 关闭（同主证明 :8391-8541 的复用）；双否半支
（:8885-8998）即 `final_neither_azim0` 在 `v' ↔ w'` 对换下的实例
（h0 换成 `azim x x' v v' = 0`，各集合/非共线事实随之对换）。难度：组装。 -/
private theorem final_azim_pi {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    {x' v' w' : V3}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (h80 : fan80 x V E)
    (hth0 : 0 < azim x u w v) (hthpi : azim x u w v < Real.pi)
    (he' : {v', w'} ∈ E) (hnc' : ¬ Collinear3 x v' w')
    (hncvw : ¬ Collinear3 x v w)
    (hx'gt : x' ∈ affGt {x} {v, w})
    (hx'gt' : x' ∈ affGt {x} {v', w'})
    (hx'ge' : x' ∈ affGe {x} {v', w'})
    (hncw' : ¬ Collinear3 x x' w') (hncv' : ¬ Collinear3 x x' v')
    (hncw : ¬ Collinear3 x x' w) (hncv : ¬ Collinear3 x x' v)
    (hpi : azim x x' v w' = Real.pi) :
    {v, w} ∈ E := by
  sorry

/-! ## 主定理（HOL planarity.hl:7788） -/

/-- HOL planarity.hl:7788 `AFF_GT_CUT_XFAN_IMP_EDGE_FAN`：`fan80` 扇中
若闭割锥 `aff_gt {x} {v,w}` 与边锥并 `xfan` 相交，则 `{v,w}` 本身是边。
setup（真证明）+ 九个切片引理的调用组装（S1-S9 如上）。 -/
theorem AFF_GT_CUT_XFAN_IMP_EDGE_FAN
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (h80 : fan80 x V E)
    (hNE : ¬(affGt {x} {v, w} ∩ xfan x V E = ∅)) :
    {v, w} ∈ E := by
  -- HOL :7801-7830：fan80 的 azim 界与基本非共线/非共面事实
  obtain ⟨hth0, hthpi⟩ := h80 u w huw
  rw [hsigma] at hth0 hthpi
  have hncvw : ¬ Collinear3 x v w := by
    have h := not_collinear_is_properties_fully_surrounded1 hfan hvu huw hth0 hthpi
      1 (by norm_num) (by norm_num)
    simpa using h
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hth0 hthpi
  have hdisvw : Disjoint ({x} : Set V3) {v, w} := disjoint_of_nc3 hncvw
  -- HOL :7831-7841：取出见证点 x'，展开 e = {v',w'}
  obtain ⟨x', hx'⟩ :=
    (Set.nonempty_iff_ne_empty (s := affGt {x} {v, w} ∩ xfan x V E)).mpr hNE
  obtain ⟨hx'gt, hx'xf⟩ := (Set.mem_inter_iff _ _ _).mp hx'
  have hx'e0 : ∃ e, e ∈ E ∧ x' ∈ affGe {x} e := hx'xf
  obtain ⟨e, he, hx'e⟩ := hx'e0
  obtain ⟨v', w', hvw'⟩ := expand_edge_graph_fan hfan he
  have he' : {v', w'} ∈ E := hvw' ▸ he
  rw [hvw'] at hx'e
  obtain ⟨hv'V, hw'V⟩ := fan_mem_of_edge hfan he'
  have hnc' : ¬ Collinear3 x v' w' := fan_not_collinear hfan he'
  have hdis' : Disjoint ({x} : Set V3) {v', w'} := disjoint_of_nc3 hnc'
  -- HOL :7843-7856：VUT（aff_gt 系数）与 VUT1（aff_ge 系数）
  rw [aff_gt_1_2 hdisvw, Set.mem_setOf_eq] at hx'gt
  obtain ⟨t1, t2, t3, ht2, ht3, htsum, hx'vw⟩ := hx'gt
  have hx'gt0 : x' ∈ affGt {x} {v, w} := by
    rw [aff_gt_1_2 hdisvw]
    exact ⟨t1, t2, t3, ht2, ht3, htsum, hx'vw⟩
  rw [aff_ge_1_2 hdis', Set.mem_setOf_eq] at hx'e
  obtain ⟨t1', t2', t3', hge2', hge3', htsum', hx'v'w'⟩ := hx'e
  have hx'e0 : x' ∈ affGe {x} {v', w'} := by
    rw [aff_ge_1_2 hdis']
    exact ⟨t1', t2', t3', hge2', hge3', htsum', hx'v'w'⟩
  -- 主情形分裂：t3' = 0（HOL :7840 THENL 1）
  by_cases ht3' : t3' = 0
  · have hsum2 : t1' + t2' = 1 := by rw [ht3'] at htsum'; linarith
    have hx'2 : x' = t1' • x + t2' • v' := by
      rw [hx'v'w', ht3']; simp
    by_cases ht2' : t2' = 0
    · -- HOL :7847-7888（S1）
      have hx1 : x' = t1' • x := by rw [hx'2, ht2']; simp
      exact (absurd_degenerate_x' (s1 := t1') (by linarith) hx1 hx'vw ht3 htsum
        hncvw).elim
    · -- HOL :7890-8013（S2 + S3 + S7）
      have hlt2' : 0 < t2' := lt_of_le_of_ne hge2' (Ne.symm ht2')
      have hv'gt : v' ∈ affGt {x} {v, w} :=
        mem_affGt_of_eq hdisvw hlt2' hsum2 hx'2 ht2 ht3 htsum hx'vw
      rw [aff_gt_1_2 hdisvw, Set.mem_setOf_eq] at hv'gt
      obtain ⟨s1, s2, s3, hs2, hs3, hssum, hsv⟩ := hv'gt
      have hv'gt' : v' ∈ affGt {x} {v, w} := by
        rw [aff_gt_1_2 hdisvw]
        exact ⟨s1, s2, s3, hs2, hs3, hssum, hsv⟩
      have hcopv' : ¬ Coplanar ({x, v', v, u} : Set V3) :=
        coplanar_transfer hs3 hssum hsv hcop
      obtain ⟨u1, hu1, ha0, hapi⟩ :=
        exists_element_in_half_sapace_fan x v' v u V E hfan hv'V hcopv'
          (hcard v' hv'V) h80
      have hncvu1 : ¬ Collinear3 x v' u1 := fan_not_collinear hfan hu1
      have hsub : affGt {x} {v', u1} ⊆ xfan x V E := fun z hz =>
        ⟨{v', u1}, hu1, aff_gt_subset_aff_ge (disjoint_of_nc3 hncvu1) hz⟩
      exact (cut_contra hfan hvu huw hsigma hcard h80 hncvu1 hv'gt'
        ha0 hapi hsub).elim
  · -- t3' > 0
    have hlt3' : 0 < t3' := lt_of_le_of_ne hge3' (Ne.symm ht3')
    by_cases ht2' : t2' = 0
    · -- HOL :8015-8153（S2 + S3 + S7 的 w' 镜像）
      have hsum3 : t1' + t3' = 1 := by rw [ht2'] at htsum'; linarith
      have hx'3 : x' = t1' • x + t3' • w' := by
        rw [hx'v'w', ht2']; simp
      have hw'gt : w' ∈ affGt {x} {v, w} :=
        mem_affGt_of_eq hdisvw hlt3' hsum3 hx'3 ht2 ht3 htsum hx'vw
      rw [aff_gt_1_2 hdisvw, Set.mem_setOf_eq] at hw'gt
      obtain ⟨s1, s2, s3, hs2, hs3, hssum, hsw⟩ := hw'gt
      have hw'gt' : w' ∈ affGt {x} {v, w} := by
        rw [aff_gt_1_2 hdisvw]
        exact ⟨s1, s2, s3, hs2, hs3, hssum, hsw⟩
      have hcopw' : ¬ Coplanar ({x, w', v, u} : Set V3) :=
        coplanar_transfer hs3 hssum hsw hcop
      obtain ⟨u1, hu1, ha0, hapi⟩ :=
        exists_element_in_half_sapace_fan x w' v u V E hfan hw'V hcopw'
          (hcard w' hw'V) h80
      have hncwu1 : ¬ Collinear3 x w' u1 := fan_not_collinear hfan hu1
      have hsub : affGt {x} {w', u1} ⊆ xfan x V E := fun z hz =>
        ⟨{w', u1}, hu1, aff_gt_subset_aff_ge (disjoint_of_nc3 hncwu1) hz⟩
      exact (cut_contra hfan hvu huw hsigma hcard h80 hncwu1 hw'gt'
        ha0 hapi hsub).elim
    · -- HOL :8155-8998（一般情形 t2' > 0 且 t3' > 0）
      have hlt2' : 0 < t2' := lt_of_le_of_ne hge2' (Ne.symm ht2')
      -- HOL :8156-8201（aff 组合，直接证明）
      have hx'gt' : x' ∈ affGt {x} {v', w'} := by
        rw [aff_gt_1_2 hdis', Set.mem_setOf_eq]
        exact ⟨t1', t2', t3', hlt2', hlt3', htsum', hx'v'w'⟩
      -- HOL :8202-8330（四条非共线，S4-S6）
      have hnc7 : ¬ Collinear3 x x' w' :=
        nc3_x'_of_combo hlt2' htsum' hx'v'w' hnc'
      have hsum8 : t1' + t3' + t2' = 1 := by linarith
      have hnc8 : ¬ Collinear3 x x' v' := by
        apply nc3_x'_of_combo hlt3' hsum8 _ (fun h => hnc' (coll3_swap' h))
        rw [hx'v'w']; module
      have hnc9 : ¬ Collinear3 x x' w := nc3_x'_w ht2 htsum hx'vw hncvw
      have hnc10 : ¬ Collinear3 x x' v := nc3_x'_v ht3 htsum hx'vw hncvw
      -- azim 三分（HOL :8330）
      by_cases hmid : 0 < azim x x' v w' ∧ azim x x' v w' < Real.pi
      · -- HOL :8331-8352
        have hsub : affGt {x} {x', w'} ⊆ xfan x V E := fun z hz =>
          ⟨{v', w'}, he', aff_gt1_subset_aff_ge hdis' hnc7 hx'e0 hz⟩
        exact (cut_contra hfan hvu huw hsigma hcard h80 hnc7 hx'gt0 hmid.1
          hmid.2 hsub).elim
      · have hge : 0 ≤ azim x x' v w' := azim_nonneg x x' v w'
        rcases eq_or_lt_of_le hge with h0 | hpos
        · -- HOL :8388-8712：azim = 0
          by_cases hw'gt : w' ∈ affGt {x} {v, w}
          · -- HOL :8391-8465（S3 + S7）
            rw [aff_gt_1_2 hdisvw, Set.mem_setOf_eq] at hw'gt
            obtain ⟨s1, s2, s3, hs2, hs3, hssum, hsw⟩ := hw'gt
            have hw'gt' : w' ∈ affGt {x} {v, w} := by
              rw [aff_gt_1_2 hdisvw]
              exact ⟨s1, s2, s3, hs2, hs3, hssum, hsw⟩
            have hcopw' : ¬ Coplanar ({x, w', v, u} : Set V3) :=
              coplanar_transfer hs3 hssum hsw hcop
            obtain ⟨u1, hu1, ha0, hapi⟩ :=
              exists_element_in_half_sapace_fan x w' v u V E hfan hw'V hcopw'
                (hcard w' hw'V) h80
            have hncwu1 : ¬ Collinear3 x w' u1 := fan_not_collinear hfan hu1
            have hsub : affGt {x} {w', u1} ⊆ xfan x V E := fun z hz =>
              ⟨{w', u1}, hu1, aff_gt_subset_aff_ge (disjoint_of_nc3 hncwu1) hz⟩
            exact (cut_contra hfan hvu huw hsigma hcard h80 hncwu1
              hw'gt' ha0 hapi hsub).elim
          · by_cases hv'gt : v' ∈ affGt {x} {v, w}
            · -- HOL :8466-8541（S3 + S7 的 v' 半支）
              rw [aff_gt_1_2 hdisvw, Set.mem_setOf_eq] at hv'gt
              obtain ⟨s1, s2, s3, hs2, hs3, hssum, hsv⟩ := hv'gt
              have hv'gt' : v' ∈ affGt {x} {v, w} := by
                rw [aff_gt_1_2 hdisvw]
                exact ⟨s1, s2, s3, hs2, hs3, hssum, hsv⟩
              have hcopv' : ¬ Coplanar ({x, v', v, u} : Set V3) :=
                coplanar_transfer hs3 hssum hsv hcop
              obtain ⟨u1, hu1, ha0, hapi⟩ :=
                exists_element_in_half_sapace_fan x v' v u V E hfan hv'V hcopv'
                  (hcard v' hv'V) h80
              have hncvu1 : ¬ Collinear3 x v' u1 := fan_not_collinear hfan hu1
              have hsub : affGt {x} {v', u1} ⊆ xfan x V E := fun z hz =>
                ⟨{v', u1}, hu1, aff_gt_subset_aff_ge (disjoint_of_nc3 hncvu1) hz⟩
              exact (cut_contra hfan hvu huw hsigma hcard h80 hncvu1
                hv'gt' ha0 hapi hsub).elim
            · -- HOL :8542-8712（S8）
              exact final_neither_azim0 hfan hvu he' hnc' hx'gt0 hx'gt' hx'e0
                hnc7 hnc8 hnc9 hnc10 h0.symm hw'gt hv'gt
        · -- 0 < azim 且 ≥ π
          have hpile : Real.pi ≤ azim x x' v w' :=
            le_of_not_gt (fun hlt => hmid ⟨hpos, hlt⟩)
          rcases eq_or_lt_of_le hpile with hpi | hpilt
          · -- HOL :8714-8998（S9）
            exact final_azim_pi hfan hvu huw hsigma hcard h80 hth0 hthpi he' hnc'
              hncvw hx'gt0 hx'gt' hx'e0 hnc7 hnc8 hnc9 hnc10 hpi.symm
          · -- HOL :8353-8438（π < azim：sum5_azim_fan 归约 + S7）
            have hxx' : x' ≠ x := by
              intro heq
              apply hnc10
              rw [heq]
              exact collinear3_of_eq rfl
            have hpivw' : azim x x' v' w' = Real.pi :=
              aff_gt2_subset_aff_ge hdis' hnc7 hnc8 hx'gt'
            have hle5 : azim x x' v' w' ≤ azim x x' v w' := by
              rw [hpivw']
              exact le_of_lt hpilt
            have hsum5 := sum5_azim_fan (x := x) (v := x') (u := v) (w1 := v')
              (w2 := w') hxx' hnc10 hnc8 hnc7 hle5
            have hkey : azim x x' v w' = azim x x' v v' + Real.pi := by
              rw [hsum5, hpivw']
            have hv'lt : azim x x' v v' < Real.pi := by
              have h2pi := azim_lt_two_pi x x' v w'
              linarith
            have hv'pos : 0 < azim x x' v v' := by linarith
            have hdiswv' : Disjoint ({x} : Set V3) {w', v'} :=
              disjoint_of_nc3 (fun h => hnc' (coll3_swap' h))
            have hx'ge2 : x' ∈ affGe {x} {w', v'} := by
              rw [pair_comm_set w' v']; exact hx'e0
            have hsub1 : affGt {x} {x', v'} ⊆ affGe {x} {w', v'} :=
              aff_gt1_subset_aff_ge hdiswv' hnc8 hx'ge2
            rw [pair_comm_set w' v'] at hsub1
            have hsub : affGt {x} {x', v'} ⊆ xfan x V E := fun z hz =>
              ⟨{v', w'}, he', hsub1 hz⟩
            exact (cut_contra hfan hvu huw hsigma hcard h80 hnc8 hx'gt0 hv'pos
              hv'lt hsub).elim

end Kepler.Text

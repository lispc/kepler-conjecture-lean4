/-
Kepler.Text.Fan — Flyspeck fan 章定义层（`fan/fan_defs.hl`，304 行）

源：`reference/flyspeck/text_formalization/fan/fan_defs.hl`（经
`general/sphere.hl` 与 HOL Light `Multivariate/flyspeck.ml` 取 azim/wedge/
aff_ge 词汇，见 `Kepler/Geom/Azim.lean` 与 `Kepler/Geom/Aff.lean`）。

移植注记：
- dart 为二元组 `V3 × V3`（HOL fan 章约定；4 元组对应物 `iFan`/
  `extendedDart`/`contractedDart` 一并移植）。
- `hypermapOfFan` 与 `conforming_bijection` **暂缓**：我们的 `Hypermap`
  结构携带 `Equiv.Perm` 与 `PermutesOn` 证明，而 e/n/f_fan 的置换性是
  fan.hl 的定理（后续块）；届时以证明参数化的 def 落地（同 `IsMarked`
  的 hnf 提参模式）。
- `yfan_deprecated`（HOL 注释认定有误）与被注释掉的 `cw_dart_fan` 不移植。
- 选择算子 `@` ↔ `Classical.epsilon`；HOL `CARD s > 1` 的有限性前提由
  `Set.ncard` 的无限集取 0 约定蕴含。
-/

import Kepler.Geom.AzimLemmas
import Kepler.Geom.Aff
import Mathlib.Topology.Connected.Basic

open Classical
open Complex

namespace Kepler.Text.Fan

open Kepler.Geom

variable {x y v u w : V3} {V : Set V3} {E : Set (Set V3)}

/-! ## fan 公理（fan_defs.hl:36–52） -/

/-- HOL `graph E`：每条边恰含两点（HAS_SIZE 2 的显式有限版）。 -/
def Graph (E : Set (Set V3)) : Prop :=
  ∀ e ∈ E, ∃ h : e.Finite, h.toFinset.card = 2

/-- HOL `fan1`：基数非平凡（有限非空）。 -/
def fan1 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop := V.Finite ∧ V ≠ ∅

/-- HOL `fan2`：原点不在顶点集。 -/
def fan2 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop := x ∉ V

/-- HOL `fan6`：无平行边（任一边与原点不共线）。 -/
def fan6 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ e ∈ E, ¬ Collinear ℝ (insert x e)

/-- HOL `fan7`：相交性（aff_ge 半空间在边上的分配律）。 -/
def fan7 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
    affGe {x} e1 ∩ affGe {x} e2 = affGe {x} (e1 ∩ e2)

/-- HOL `FAN(x,V,E)`。 -/
def FAN (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧ fan7 x V E

/-! ## 邻边与 σ 映射（fan_defs.hl:55–85） -/

/-- HOL `set_of_edge v V E`：`v` 的邻居集。 -/
def setOfEdge (v : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  {w | {v, w} ∈ E ∧ w ∈ V}

/-- HOL `sigma_fan x V E v u`：`u` 之后的下一邻居（方位角最小者；唯一
邻居时回自身）。 -/
noncomputable def sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3) :
    V3 :=
  if setOfEdge v V E = {u} then u
  else Classical.epsilon (fun w => w ∈ setOfEdge v V E ∧ w ≠ u ∧
    ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u w ≤ azim x v u w1)

/-- HOL `extension_sigma_fan`：邻居集外恒等。 -/
noncomputable def extensionSigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : V3 :=
  if u ∉ setOfEdge v V E then u else sigmaFan x V E v u

/-- HOL `inverse_sigma_fan`（函数逆；HOL `inverse` ↔ `Function.invFun`）。 -/
noncomputable def inverseSigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) : V3 → V3 :=
  Function.invFun (extensionSigmaFan x V E v)

/-! ## fan 的 dart（fan_defs.hl:88–128） -/

/-- HOL `dart1_of_fan (V,E)`：真 dart（有边的对）。 -/
def dart1OfFan (V : Set V3) (E : Set (Set V3)) : Set (V3 × V3) :=
  {d | {d.1, d.2} ∈ E}

/-- HOL `dart_of_fan (V,E)`：dart 集（孤立点补 (v,v)）。 -/
def dartOfFan (V : Set V3) (E : Set (Set V3)) : Set (V3 × V3) :=
  {d | d.1 = d.2 ∧ d.1 ∈ V ∧ setOfEdge d.1 V E = ∅} ∪ dart1OfFan V E

/-- HOL `i_fan`：4 元组对应物（(x,v,w,w) ↦ (x,v,w,σ w)）。 -/
noncomputable def iFan (x : V3) (V : Set V3) (E : Set (Set V3)) :
    V3 × V3 × V3 × V3 → V3 × V3 × V3 × V3 :=
  fun p => (p.1, p.2.1, p.2.2.1, sigmaFan x V E p.2.1 p.2.2.2)

/-- HOL `extended_dart (V,E) (v,w)`。 -/
noncomputable def extendedDart (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 × V3 × V3 :=
  iFan 0 V E (0, d.1, d.2, d.2)

/-- HOL `contracted_dart`。 -/
def contractedDart (p : V3 × V3 × V3 × V3) : V3 × V3 := (p.2.1, p.2.2.1)

/-! ## e/n/f 映射（fan_defs.hl:131–150） -/

/-- HOL `e_fan_pair (V,E) (v,w) = (w,v)`。 -/
def eFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : V3 × V3 :=
  (d.2, d.1)

/-- HOL `n_fan_pair (V,E) (v,w) = (v, σ_v w)`（原点取 `vec 0`）。 -/
noncomputable def nFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  (d.1, sigmaFan 0 V E d.1 d.2)

/-- HOL `f_fan_pair (V,E) (v,w) = (w, σ⁻¹_ w v)`。 -/
noncomputable def fFanPair (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  (d.2, inverseSigmaFan 0 V E d.2 d.1)

/-- HOL `res f s`（sphere.hl:503）：集合外恒等的限制。 -/
noncomputable def res {α : Type*} (f : α → α) (s : Set α) : α → α :=
  fun a => if a ∈ s then f a else a

/-- HOL `e_fan_pair_ext`（= `res (e_fan_pair) (dart1_of_fan)`，见
`eFanPairExt_eq`）。 -/
noncomputable def eFanPairExt (V : Set V3) (E : Set (Set V3)) :
    V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then eFanPair V E d else d

/-- HOL `n_fan_pair_ext`。 -/
noncomputable def nFanPairExt (V : Set V3) (E : Set (Set V3)) : V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then nFanPair V E d else d

/-- HOL `f_fan_pair_ext`。 -/
noncomputable def fFanPairExt (V : Set V3) (E : Set (Set V3)) : V3 × V3 → V3 × V3 :=
  fun d => if d ∈ dart1OfFan V E then fFanPair V E d else d

theorem eFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    eFanPairExt V E = res (eFanPair V E) (dart1OfFan V E) := rfl

theorem nFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    nFanPairExt V E = res (nFanPair V E) (dart1OfFan V E) := rfl

theorem fFanPairExt_eq (V : Set V3) (E : Set (Set V3)) :
    fFanPairExt V E = res (fFanPair V E) (dart1OfFan V E) := rfl

/-! ## x/y 区域与楔形（fan_defs.hl:155–234） -/

/-- HOL `xfan (x,V,E)`：被边锥覆盖的区域。 -/
def xfan (x : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  {v | ∃ e ∈ E, v ∈ affGe {x} e}

/-- HOL `yfan (x,V,E)` = 全空间 \\ xfan。 -/
def yfan (x : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  Set.univ \ xfan x V E

/-- HOL `w_dart_fan x V E (y,v,w,w1)`。 -/
def wDartFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : V3 × V3 × V3 × V3) : Set V3 :=
  if (setOfEdge p.2.1 V E).ncard > 1 then
    wedge x p.2.1 p.2.2.1 (sigmaFan x V E p.2.1 p.2.2.1)
  else if setOfEdge p.2.1 V E = {p.2.2.1} then
    Set.univ \ affGe {x, p.2.1} {p.2.2.1}
  else if setOfEdge p.2.1 V E = ∅ then
    Set.univ \ (affineSpan ℝ ({x, p.2.1} : Set V3) : Set V3)
  else ∅

/-- HOL `cwedge v0 v1 w1 w2`。 -/
def cwedge (v0 v1 w1 w2 : V3) : Set V3 :=
  {y | 0 ≤ azim v0 v1 w1 y ∧ azim v0 v1 w1 y ≤ azim v0 v1 w1 w2}

/-- HOL `azim_fan x V E v w`。 -/
noncomputable def azimFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v w : V3) :
    ℝ :=
  if (setOfEdge v V E).ncard > 1 then azim x v w (sigmaFan x V E v w)
  else 2 * Real.pi

/-- HOL `azim_dart (V,E) (v,w)`。 -/
noncomputable def azimDart (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) : ℝ :=
  if d.1 = d.2 then 2 * Real.pi else azimFan 0 V E d.1 d.2

/-- HOL `rcone_fan x v h`：半角锥。 -/
def rconeFan (x v : V3) (h : ℝ) : Set V3 :=
  {b | ((b - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) >
    dist b x * dist v x * h}

/-- HOL `rw_dart_fan x V E (y,v,w,w1) h`。 -/
def rwDartFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : V3 × V3 × V3 × V3) (h : ℝ) : Set V3 :=
  wDartFan x V E p ∩ rconeFan x p.2.1 h

/-! ## 拓扑分量与引导（fan_defs.hl:244–275） -/

/-- HOL `topological_component_yfan (x,V,E)`。 -/
def topologicalComponentYfan (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set (Set V3) :=
  {connectedComponentIn (yfan x V E) b | b ∈ yfan x V E}

/-- HOL `dart_leads_into1 (x,V,E) (v,u)`。 -/
noncomputable def dartLeadsInto1 (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : Set V3 :=
  Classical.epsilon (fun s => s ∈ topologicalComponentYfan x V E ∧
    ∃ eps < 1, rwDartFan x V E (x, v, u, sigmaFan x V E v u) eps ⊆ s)

/-- HOL `dartset_leads_into (x,V,E) ds`。 -/
noncomputable def dartsetLeadsInto (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) : Set V3 :=
  Classical.epsilon (fun s => ∀ b ∈ ds, s = dartLeadsInto1 x V E b.1 b.2)

/-- HOL `surrounded_node (V,E) v`。 -/
def surroundedNode (V : Set V3) (E : Set (Set V3)) (v : V3) : Prop :=
  ∀ d ∈ dartOfFan V E, d.1 = v → azimDart V E d < Real.pi

/-- HOL `fully_surrounded (V,E)`。 -/
def fullySurrounded (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ d ∈ dartOfFan V E, azimDart V E d < Real.pi

/-- HOL `fan81`。 -/
def fan81 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E → azimFan x V E v u < Real.pi

/-- HOL `fan80`。 -/
def fan80 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E →
    0 < azim x v u (sigmaFan x V E v u) ∧ azim x v u (sigmaFan x V E v u) < Real.pi


/-! ## fan_misc.hl（155 行）的可独立部分

其余三引理（`INVERSE_SIGMA_FAN`、`EXTENSION_SIGMA_FAN_INJECTIVE`、
`INVERSE_SIGMA_FAN_EQ_INVERSE1_SIGMA_FAN`）依赖 fan.hl 的
`permutes_sigma_fan`/`INVERSE1_SIGMA_FAN`（σ-置换理论，进而依赖
flyspeck.ml 的 azim 基础引理层 AZIM_REFL/AZIM_SYMM 等）——排入 F3。 -/

/-- HOL fan_misc `inverse1_sigma_fan`（ε-形式的三条件逆）。 -/
noncomputable def inverse1SigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) : V3 → V3 :=
  Classical.epsilon (fun g => (∀ w : V3, {v, w} ∈ E → {v, g w} ∈ E) ∧
    (∀ w : V3, {v, w} ∈ E → sigmaFan x V E v (g w) = w) ∧
    (∀ w : V3, {v, w} ∈ E → g (sigmaFan x V E v w) = w))

/-- HOL fan_misc `EXTENSION_SIGMA_FAN_EQ_RES`。 -/
theorem extensionSigmaFan_eq_res (x : V3) (V : Set V3) (E : Set (Set V3))
    (v : V3) :
    extensionSigmaFan x V E v = res (sigmaFan x V E v) (setOfEdge v V E) := by
  funext u
  unfold extensionSigmaFan res
  by_cases hu : u ∈ setOfEdge v V E <;> simp [hu]

/-- HOL fan_misc `IN_SET_OF_EDGE`。 -/
theorem in_setOfEdge (V : Set V3) (E : Set (Set V3)) (v w : V3)
    (hsub : ⋃₀ E ⊆ V) (hd : (v, w) ∈ dart1OfFan V E) :
    v ∈ V ∧ w ∈ V ∧ w ∈ setOfEdge v V E ∧ v ∈ setOfEdge w V E := by
  have he : {v, w} ∈ E := hd
  have hv : v ∈ V := hsub (Set.mem_sUnion.mpr ⟨{v, w}, he, by simp⟩)
  have hw : w ∈ V := hsub (Set.mem_sUnion.mpr ⟨{v, w}, he, by simp⟩)
  have he' : {w, v} ∈ E := by
    have h2 : ({w, v} : Set V3) = ({v, w} : Set V3) := by
      apply Set.ext; intro a; simp; tauto
    rw [h2]; exact he
  exact ⟨hv, hw, ⟨he, hw⟩, ⟨he', hv⟩⟩

/-- HOL fan_misc `FAN_IN_SET_OF_EDGE`。 -/
theorem FAN_in_setOfEdge (x : V3) (V : Set V3) (E : Set (Set V3)) (v w : V3)
    (hfan : FAN x V E) (he : {v, w} ∈ E) :
    v ∈ V ∧ w ∈ V ∧ w ∈ setOfEdge v V E ∧ v ∈ setOfEdge w V E :=
  in_setOfEdge V E v w hfan.1 he


/-! ## σ-链起步：SIGMA_FAN spec 与集隶属（fan.hl:324/330/552/565） -/

/-- HOL fan.hl:324 `remark_finite_fan1`。 -/
theorem remark_finite_fan1 (v : V3) (V : Set V3) (E : Set (Set V3))
    (hV : V.Finite) : (setOfEdge v V E).Finite :=
  hV.subset (fun w hw => hw.2)

/-- HOL fan.hl:330 `properties_of_set_of_edge`。 -/
theorem properties_of_setOfEdge (v : V3) (V : Set V3) (E : Set (Set V3)) (u : V3)
    (hsub : ⋃₀ E ⊆ V) : ({v, u} ∈ E ↔ u ∈ setOfEdge v V E) := by
  constructor
  · intro he
    refine ⟨he, ?_⟩
    exact hsub (Set.mem_sUnion.mpr ⟨{v, u}, he, by simp⟩)
  · intro h
    exact h.1

/-- HOL fan.hl `exists_sigma_fan`（最小方位角见证的存在性）。 -/
theorem exists_sigmaFan (hne : setOfEdge v V E ≠ {u}) (hfan : FAN x V E)
    (hu : u ∈ setOfEdge v V E) :
    ∃ w : V3, w ∈ setOfEdge v V E ∧ w ≠ u ∧
      ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u w ≤ azim x v u w1 := by
  obtain ⟨hsub, -, ⟨hV, -⟩, -⟩ := hfan
  have hfin := remark_finite_fan1 v V E hV
  -- setOfEdge \ {u} 非空
  have hne2 : (setOfEdge v V E \ {u}).Nonempty := by
    by_contra hempty
    apply hne
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨hu, ?_⟩
    intro w hw
    by_contra hwu
    exact hempty ⟨w, ⟨hw, by simp [hwu]⟩⟩
  -- 有限非空实值集存在最小元
  have hfin2 : (setOfEdge v V E \ {u}).Finite :=
    hfin.subset (fun w hw => hw.1)
  obtain ⟨w, hwmem, hwmin⟩ :=
    Set.exists_min_image (setOfEdge v V E \ {u}) (fun w => azim x v u w) hfin2 hne2
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hwmem
  exact ⟨w, hwmem.1, hwmem.2, fun w1 hw1 hw1u => hwmin w1 ⟨hw1, by simp [hw1u]⟩⟩


/-- HOL fan.hl:552 `SIGMA_FAN`（σ 的 ε-witness 三条件）。 -/
theorem SIGMA_FAN (hne : setOfEdge v V E ≠ {u}) (hfan : FAN x V E)
    (hu : u ∈ setOfEdge v V E) :
    sigmaFan x V E v u ∈ setOfEdge v V E ∧ sigmaFan x V E v u ≠ u ∧
      ∀ w1 ∈ setOfEdge v V E, w1 ≠ u → azim x v u (sigmaFan x V E v u) ≤ azim x v u w1 := by
  unfold sigmaFan
  rw [if_neg hne]
  exact Classical.epsilon_spec (exists_sigmaFan hne hfan hu)

/-- HOL fan.hl:565 `sigma_fan_in_set_of_edge`。 -/
theorem sigma_fan_in_setOfEdge (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E) :
    sigmaFan x V E v u ∈ setOfEdge v V E := by
  by_cases h : setOfEdge v V E = {u}
  · rw [sigmaFan, if_pos h, h]
    exact Set.mem_singleton u
  · exact (SIGMA_FAN h hfan hu).1

/-- HOL fan.hl:337 `properties_of_set_of_edge_fan`。 -/
theorem properties_of_setOfEdge_fan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (hfan : FAN x V E) : {v, u} ∈ E ↔ u ∈ setOfEdge v V E :=
  properties_of_setOfEdge v V E u hfan.1


/-! ## 唯一性与角加法（fan.hl:612/634/711/726/1646） -/

/-- 边与原点不共线（fan6 的直接推论）。 -/
theorem fan_not_collinear (hfan : FAN x V E) (he : {v, u} ∈ E) :
    ¬ Collinear3 x v u :=
  hfan.2.2.2.2.1 _ he

theorem fan_mem_of_edge (hfan : FAN x V E) (he : {v, u} ∈ E) :
    v ∈ V ∧ u ∈ V := by
  obtain ⟨hsub, -⟩ := hfan
  exact ⟨hsub (Set.mem_sUnion.mpr ⟨{v, u}, he, by simp⟩),
    hsub (Set.mem_sUnion.mpr ⟨{v, u}, he, by simp⟩)⟩

/-- HOL fan.hl:634 `UNIQUE1_POINT_FAN`（aff_gt 射线上的点唯一）。 -/
theorem unique1_point_fan (hfan : FAN x V E) (hu : {v, u} ∈ E) (hw : {v, w} ∈ E)
    (hmem : w ∈ affGt {x, v} {u}) : u = w := by
  obtain ⟨hsub, hgraph, hf1, hfan2, hfan6, hfan7⟩ := hfan
  obtain ⟨hvV, huV⟩ := fan_mem_of_edge ⟨hsub, hgraph, hf1, hfan2, hfan6, hfan7⟩ hu
  obtain ⟨-, hwV⟩ := fan_mem_of_edge ⟨hsub, hgraph, hf1, hfan2, hfan6, hfan7⟩ hw
  have hnc : ¬ Collinear3 x v u := hfan6 _ hu
  have hncw : ¬ Collinear3 x v w := hfan6 _ hw
  have hxv : x ≠ v := fun he => hfan2 (he ▸ hvV)
  have hxu : x ≠ u := fun he => hfan2 (he ▸ huV)
  have hxw : x ≠ w := fun he => hfan2 (he ▸ hwV)
  have hvu : v ≠ u := by
    intro he
    apply hnc
    rw [he]
    exact collinear3_pair_right rfl
  have hvw : v ≠ w := by
    intro he
    apply hncw
    rw [he]
    exact collinear3_pair_right rfl
  obtain ⟨c, hc, h, hcoeff⟩ := affGt_pair_iff (v0 := x) (v1 := v) (x := u)
    (y := w) hxv (Ne.symm hxu) (Ne.symm hvu) |>.mp hmem
  have hcne : c ≠ 0 := ne_of_gt hc
  have hin : {v, u} ∈ E ∪ {s | ∃ a ∈ V, s = {a}} := Or.inl hu
  have hin2 : {v, w} ∈ E ∪ {s | ∃ a ∈ V, s = {a}} := Or.inl hw
  by_contra huw
  have hint : ({v, u} ∩ {v, w} : Set V3) = {v} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz1 | hz1, hz2 | hz2⟩
      all_goals first
        | exact hz2
        | exact hz1
        | exact absurd (hz1.symm.trans hz2) huw
        | exact absurd (hz1.symm.trans hz2) (Ne.symm hvu)
        | exact absurd (hz1.symm.trans hz2) hvw
    · intro rfl
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  have hinter : affGe {x} {v, u} ∩ affGe {x} {v, w} = affGe {x} {v} := by
    rw [hfan7 {v, u} hin {v, w} hin2, hint]
  have hcontra : ∀ t : ℝ, u - x = t • (v - x) → False := fun t ht =>
    hnc ((collinear3_iff_smul (w := v) (v := x) (w1 := u) (Ne.symm hxv)).mpr
      ⟨t, ht⟩)
  by_cases hge : 0 ≤ h
  · have hwmem1 : w ∈ affGe {x} {v, u} := by
      show Affsign (fun r => 0 ≤ r) {x} {v, u} w
      refine Affsign.of_triple h c hge hc.le ?_ hxv hxu hvu
      rw [show w = (w - x) + x from (sub_add_cancel w x).symm, hcoeff]
      module
    have hwmem2 : w ∈ affGe {x} {v, w} := by
      show Affsign (fun r => 0 ≤ r) {x} {v, w} w
      exact Affsign.of_triple 0 1 le_rfl zero_le_one (by module) hxv hxw hvw
    obtain ⟨t, ht⟩ := affGe_ray (x := x) (v := v) hxv
      ((hinter ▸ Set.mem_inter hwmem1 hwmem2) : w ∈ affGe {x} {v})
    have hkey : c • (u - x) = t • (v - x) - h • (v - x) := by
      rw [eq_sub_iff_add_eq, ← hcoeff, ht]
    rcases eq_or_ne t h with rfl | hne
    · rw [sub_self] at hkey
      rcases smul_eq_zero.mp hkey with h0 | h0
      · exact hcne h0
      · exact hxu (sub_eq_zero.mp h0).symm
    · exact hcontra ((t - h) / c) (by
        have h1 : c • (u - x) = c • (((t - h) / c) • (v - x)) := by
          rw [smul_smul, mul_div_cancel₀ _ hcne, sub_smul]
          exact hkey
        have h2 := smul_eq_zero.mp (by rw [smul_sub, h1, sub_self] : c • ((u - x) -
          ((t - h) / c) • (v - x)) = 0)
        rcases h2 with h3 | h3
        · exact absurd h3 hcne
        · exact sub_eq_zero.mp h3)
  · have hlt : h < 0 := lt_of_not_ge hge
    have hco1 : c • (u - x) = (w - x) - h • (v - x) := by
      rw [eq_sub_iff_add_eq, hcoeff]
    have hux : u - x = (1 / c) • (w - x) + (-h / c) • (v - x) := by
      have h1 : c • (u - x) = c • ((1 / c) • (w - x) + (-h / c) • (v - x)) := by
        rw [smul_add, smul_smul, smul_smul,
          mul_div_cancel₀ _ hcne, one_smul,
          show c * (-h / c) = -h by field_simp, hco1, sub_eq_add_neg, neg_smul]
      have h2 := smul_eq_zero.mp (by rw [smul_sub, h1, sub_self] :
        c • ((u - x) - ((1 / c) • (w - x) + (-h / c) • (v - x))) = 0)
      rcases h2 with h3 | h3
      · exact absurd h3 hcne
      · exact sub_eq_zero.mp h3
    have humem1 : u ∈ affGe {x} {v, u} := by
      show Affsign (fun r => 0 ≤ r) {x} {v, u} u
      exact Affsign.of_triple 0 1 le_rfl zero_le_one (by module) hxv hxu hvu
    have humem2 : u ∈ affGe {x} {v, w} := by
      show Affsign (fun r => 0 ≤ r) {x} {v, w} u
      have hlt0 : (0:ℝ) < -h / c := by
        have h1 : (0:ℝ) < -h := by linarith
        positivity
      refine Affsign.of_triple (-h / c) (1 / c) hlt0.le (by positivity)
        ?_ hxv hxw hvw
      rw [show u = (u - x) + x from (sub_add_cancel u x).symm, hux]
      module
    obtain ⟨t, ht⟩ := affGe_ray (x := x) (v := v) hxv
      ((hinter ▸ Set.mem_inter humem1 humem2) : u ∈ affGe {x} {v})
    exact hcontra t ht



/-- HOL fan.hl:726 `UNIQUE_AZIM_0_POINT_FAN`。 -/
theorem unique_azim0_point_fan (hfan : FAN x V E) (hu : {v, u} ∈ E)
    (hw : {v, w} ∈ E) (h0 : azim x v u w = 0) : u = w :=
  unique1_point_fan hfan hu hw
    ((azim_eq_zero_iff_alt (v0 := x) (v1 := v) (w := u) (x := w)
      (fan_not_collinear hfan hu) (fan_not_collinear hfan hw)).mp h0)

/-- HOL fan.hl:711 `UNIQUE_AZIM_POINT_FAN`。 -/
theorem unique_azim_point_fan (hfan : FAN x V E) (hu : {v, u} ∈ E)
    (hw : {v, w} ∈ E) (hw1 : {v, w1} ∈ E)
    (heq : azim x v u w = azim x v u w1) : w = w1 :=
  unique1_point_fan (v := v) (u := w) (w := w1) hfan hw hw1
    ((azim_eq_azim_iff (v0 := x) (v1 := v) (w := u) (x := w) (y := w1)
      (fan_not_collinear hfan hu) (fan_not_collinear hfan hw)
      (fan_not_collinear hfan hw1)).mp heq)

/-- HOL fan.hl:1646 `sum2_azim_fan`（三点角加法；证明走标架极表示，
不经 cyclic_set 机制）。 -/
theorem sum2_azim_fan (hfan : FAN x V E)
    (hu : {v, u} ∈ E) (hw1 : {v, w1} ∈ E) (hw2 : {v, w2} ∈ E)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨hsub, -, -, hfan2, hfan6, -⟩ := hfan
  have hvV : v ∈ V := hsub (Set.mem_sUnion.mpr ⟨{v, u}, hu, by simp⟩)
  have hxv : v ≠ x := by
    intro he
    rw [he] at hvV
    exact hfan2 hvV
  have hncu : ¬ Collinear3 x v u := hfan6 _ hu
  have hnc1 : ¬ Collinear3 x v w1 := hfan6 _ hw1
  have hnc2 : ¬ Collinear3 x v w2 := hfan6 _ hw2
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr (fun he => hxv he))
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hncu hnc1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hncu hnc2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec hnc1 hnc2 hon hax hxv
  -- z_u 的两种极表示 ⟹ e^{iψ} = e^{iψ2}
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  -- z_{w1} 两种表示 ⟹ e^{i(ψ+θ1)} = e^{iψ'}
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  -- z_{w2} 两种表示 ⟹ e^{i(ψ2+θ2)} = e^{i(ψ'+φ)}
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  -- hE1' : e^{iψ} * e^{iθ2} = e^{iψ'} * e^{iφ}; hE2 : e^{iψ} * e^{iθ1} = e^{iψ'}
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * I)
      = Complex.exp (((ψ : ℝ) : ℂ) * I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hc3 : azim x v u w2
      = azim x v u w1 + azim x v w1 w2 + (n:ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith



/-! ## σ 的单射性与置换性（fan.hl:1974 `permutes_sigma_fan`） -/

set_option maxHeartbeats 800000 in
/-- 邻集内 σ 的单射性（HOL `mono_sigma_fan` 的实质）。 -/
theorem mono_sigma_fan (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E)
    (hw : w ∈ setOfEdge v V E)
    (heq : sigmaFan x V E v u = sigmaFan x V E v w) : u = w := by
  by_cases hne : setOfEdge v V E = {u}
  · -- 单点情形：w = u
    have hwu : w = u := by
      have := hne ▸ hw
      simpa using this
    exact hwu.symm
  · by_contra huw
    have hne2 : setOfEdge v V E ≠ {w} := by
      intro he
      have huw' : u = w := by
        have hmem : u ∈ ({w} : Set V3) := by rw [← he]; exact hu
        simpa using hmem
      exact huw huw'
    obtain ⟨hsu, hsne, hsmin⟩ := SIGMA_FAN hne hfan hu
    obtain ⟨hsw, hsne2, hsmin2⟩ := SIGMA_FAN hne2 hfan hw
    rw [← heq] at hsne2 hsmin2
    -- 边与非退化
    have hsu' : {v, sigmaFan x V E v u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfan).mpr hsu
    have hu' : {v, u} ∈ E := (properties_of_setOfEdge_fan x V E v u hfan).mpr hu
    have hw' : {v, w} ∈ E := (properties_of_setOfEdge_fan x V E v w hfan).mpr hw
    -- 极小性
    have h1 : azim x v u (sigmaFan x V E v u) ≤ azim x v u w := hsmin w hw (fun heq2 => huw heq2.symm)
    have h2 : azim x v w (sigmaFan x V E v u) ≤ azim x v w u :=
      hsmin2 u hu (fun heq2 => huw heq2)
    -- 角加法
    have hA : azim x v u w = azim x v u (sigmaFan x V E v u) + azim x v (sigmaFan x V E v u) w :=
      sum2_azim_fan hfan hu' hsu' hw' h1
    have hB : azim x v w u = azim x v w (sigmaFan x V E v u) + azim x v (sigmaFan x V E v u) u :=
      sum2_azim_fan hfan hw' hsu' hu' h2
    -- 三补角
    have hC1 : azim x v (sigmaFan x V E v u) w
        = if azim x v w (sigmaFan x V E v u) = 0 then 0 else 2 * Real.pi - azim x v w (sigmaFan x V E v u) :=
      azim_compl (z := x) (w := v) (w1 := w) (w2 := sigmaFan x V E v u)
        (fan_not_collinear hfan hw') (fan_not_collinear hfan hsu')
    have hC2 : azim x v (sigmaFan x V E v u) u
        = if azim x v u (sigmaFan x V E v u) = 0 then 0 else 2 * Real.pi - azim x v u (sigmaFan x V E v u) :=
      azim_compl (z := x) (w := v) (w1 := u) (w2 := sigmaFan x V E v u)
        (fan_not_collinear hfan hu') (fan_not_collinear hfan hsu')
    have hC3 : azim x v w u
        = if azim x v u w = 0 then 0 else 2 * Real.pi - azim x v u w :=
      azim_compl (z := x) (w := v) (w1 := u) (w2 := w)
        (fan_not_collinear hfan hu') (fan_not_collinear hfan hw')
    have hnn1 : (0:ℝ) ≤ azim x v u (sigmaFan x V E v u) := azim_nonneg x v u (sigmaFan x V E v u)
    have hnn2 : (0:ℝ) ≤ azim x v w (sigmaFan x V E v u) := azim_nonneg x v w (sigmaFan x V E v u)
    have hnn3 : (0:ℝ) ≤ azim x v (sigmaFan x V E v u) w := azim_nonneg x v (sigmaFan x V E v u) w
    have hnn4 : (0:ℝ) ≤ azim x v (sigmaFan x V E v u) u := azim_nonneg x v (sigmaFan x V E v u) u
    have hlt : azim x v u (sigmaFan x V E v u) < 2 * Real.pi := azim_lt_two_pi x v u (sigmaFan x V E v u)
    have hlt2 : azim x v u w < 2 * Real.pi := azim_lt_two_pi x v u w
    have hlt3 : azim x v w (sigmaFan x V E v u) < 2 * Real.pi := azim_lt_two_pi x v w (sigmaFan x V E v u)
    -- 情形分解
    rcases eq_or_ne (azim x v u w) 0 with hz1 | hz1
    · -- u→w 角为 0：由 A 得 sigmaFan x V E v u→w、u→sigmaFan x V E v u 均为 0 ⟹ sigmaFan x V E v u = u 矛盾
      exfalso
      rw [hz1] at hA
      have hz2 : azim x v u (sigmaFan x V E v u) = 0 := by
        have := hA
        linarith
      exact hsne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v)
        (u := u) (w := sigmaFan x V E v u) hfan hu' hsu' hz2).symm
    · -- u→w 角非 0
      rw [if_neg hz1] at hC3
      rcases eq_or_ne (azim x v w (sigmaFan x V E v u)) 0 with hz3 | hz3
      · -- w→sigmaFan x V E v u 角为 0 ⟹ w = σ w，与 σ w ≠ w 矛盾
        exfalso
        -- w = σ u；但 σ u = σ w 且 σ w ≠ w ⟹ 矛盾
        have hws : w = sigmaFan x V E v u :=
          unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v)
            (u := w) (w := sigmaFan x V E v u) hfan hw' hsu' hz3
        exact hsne2 (heq ▸ hws.symm)
      · rw [if_neg hz3] at hC1
        rcases eq_or_ne (azim x v u (sigmaFan x V E v u)) 0 with hz2 | hz2
        · exfalso
          exact hsne (unique_azim0_point_fan (x := x) (V := V) (E := E) (v := v)
            (u := u) (w := sigmaFan x V E v u) hfan hu' hsu' hz2).symm
        · rw [if_neg hz2] at hC2
          -- 纯算术矛盾：B + C1/C2/C3 + A
          exfalso
          have hsum3 : azim x v u w
              = azim x v u (sigmaFan x V E v u) + azim x v w (sigmaFan x V E v u) := by
            linarith
          have hsum1 : azim x v w u
              = (2 * Real.pi - azim x v w (sigmaFan x V E v u))
                + (2 * Real.pi - azim x v u (sigmaFan x V E v u)) := by
            linarith
          have hsum2 : azim x v w u = 2 * Real.pi - azim x v u w := by
            linarith
          linarith

/-- HOL fan.hl:1974 `permutes_sigma_fan`（setOfEdge 上的置换性）。 -/
theorem permutes_sigma_fan (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E) :
    (∀ a ∈ setOfEdge v V E, extensionSigmaFan x V E v a ∈ setOfEdge v V E)
      ∧ (∀ a ∈ setOfEdge v V E, ∀ b ∈ setOfEdge v V E,
          extensionSigmaFan x V E v a = extensionSigmaFan x V E v b → a = b)
      ∧ (∀ a ∉ setOfEdge v V E, extensionSigmaFan x V E v a = a) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [extensionSigmaFan, if_neg (by simpa using ha)]
    exact sigma_fan_in_setOfEdge hfan ha
  · intro a ha b hb heq
    rw [extensionSigmaFan, if_neg (by simpa using ha),
      extensionSigmaFan, if_neg (by simpa using hb)] at heq
    exact mono_sigma_fan hfan ha hb heq
  · intro a ha
    rw [extensionSigmaFan, if_pos ha]


/-- 有限集上的抽屉原理：映内 + 单射 ⟹ 满射。 -/
private theorem finite_surjOf_inj {f : V3 → V3} {S : Set V3} (hfin : S.Finite)
    (hmaps : ∀ a ∈ S, f a ∈ S) (hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) :
    ∀ b ∈ S, ∃ a ∈ S, f a = b := by
  have hinj' : Set.InjOn f S := fun a ha b hb hab => hinj a ha b hb hab
  have hcard : (f '' S).ncard = S.ncard := hinj'.ncard_image
  have hle : f '' S ⊆ S := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := hy
    exact hmaps a ha
  intro b hb
  by_contra hnb
  have hsub2 : f '' S ⊆ S \ {b} := by
    intro y hy
    refine ⟨hle hy, ?_⟩
    intro hyb
    rw [Set.mem_singleton_iff] at hyb
    obtain ⟨a, haS, hay⟩ := (Set.mem_image f S y).mp hy
    rw [hyb] at hay
    exact hnb ⟨a, haS, hay⟩
  have hpsub : S \ {b} ⊂ S := by
    refine ⟨fun y hy => hy.1, ?_⟩
    intro heq
    have hmem : b ∈ S \ {b} := heq hb
    exact absurd hmem.2 (by simp)
  have h2 : (S \ {b}).ncard < S.ncard := Set.ncard_lt_ncard hpsub hfin
  have hfin2 : (S \ {b}).Finite := hfin.subset (fun y hy => hy.1)
  have h3 : (f '' S).ncard ≤ (S \ {b}).ncard :=
    Set.ncard_le_ncard hsub2 hfin2
  omega

/-- σ 在 setOfEdge 上的双射性。 -/
theorem sigma_bijOn (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E) :
    Set.BijOn (sigmaFan x V E v) (setOfEdge v V E) (setOfEdge v V E) := by
  refine ⟨fun a ha => sigma_fan_in_setOfEdge hfan ha,
    fun a ha b hb heq => mono_sigma_fan hfan ha hb heq, ?_⟩
  intro b hb
  exact finite_surjOf_inj (remark_finite_fan1 v V E hfan.2.2.1.1)
    (fun a ha => sigma_fan_in_setOfEdge hfan ha)
    (fun a ha b hb heq => mono_sigma_fan hfan ha hb heq) b hb

/-- HOL fan_misc:43 `INVERSE_SIGMA_FAN`（extension 的双逆）。 -/
theorem inverse_sigma_fan_comp (hfan : FAN x V E) (hu : u ∈ setOfEdge v V E) :
    (inverseSigmaFan x V E v) ∘ (extensionSigmaFan x V E v) = id
      ∧ (extensionSigmaFan x V E v) ∘ (inverseSigmaFan x V E v) = id := by
  obtain ⟨hmaps, hinjon, hid⟩ := permutes_sigma_fan hfan hu
  have hbij : Function.Bijective (extensionSigmaFan x V E v) := by
    constructor
    · intro a b hab
      by_cases ha : a ∈ setOfEdge v V E
      · have hax : extensionSigmaFan x V E v a = sigmaFan x V E v a := by
          rw [extensionSigmaFan, if_neg (by simpa using ha)]
        by_cases hb : b ∈ setOfEdge v V E
        · have hbx : extensionSigmaFan x V E v b = sigmaFan x V E v b := by
            rw [extensionSigmaFan, if_neg (by simpa using hb)]
          rw [hax, hbx] at hab
          exact mono_sigma_fan hfan ha hb hab
        · rw [hax, hid b hb] at hab
          -- hab : σ a = b；σ a ∈ S 与 b ∉ S 矛盾
          have hsa := sigma_fan_in_setOfEdge hfan ha
          rw [hab] at hsa
          exact absurd hsa hb
      · have hax : extensionSigmaFan x V E v a = a := hid a ha
        by_cases hb : b ∈ setOfEdge v V E
        · rw [hax, extensionSigmaFan, if_neg (by simpa using hb)] at hab
          -- hab : a = σ b；σ b ∈ S 与 a ∉ S 矛盾
          have hsb := sigma_fan_in_setOfEdge hfan hb
          rw [← hab] at hsb
          exact absurd hsb ha
        · rw [hax, hid b hb] at hab
          exact hab
    · intro y
      by_cases hy : y ∈ setOfEdge v V E
      · obtain ⟨a, ha, hay⟩ :=
          finite_surjOf_inj (remark_finite_fan1 v V E hfan.2.2.1.1)
            (fun c hc => sigma_fan_in_setOfEdge hfan hc)
            (fun c hc d hd heq => mono_sigma_fan hfan hc hd heq) y hy
        refine ⟨a, ?_⟩
        rw [extensionSigmaFan, if_neg (by simpa using ha)]
        exact hay
      · exact ⟨y, hid y hy⟩
  unfold inverseSigmaFan
  constructor
  · funext y
    exact Function.leftInverse_invFun hbij.1 y
  · funext y
    exact Function.rightInverse_invFun hbij.2 y

/-- HOL fan_misc `EXTENSION_SIGMA_FAN_INJECTIVE`。 -/
theorem extension_sigma_fan_injective (hfan : FAN x V E)
    (hu : u ∈ setOfEdge v V E) :
    ∀ w1 w2, extensionSigmaFan x V E v w1 = extensionSigmaFan x V E v w2
      → w1 = w2 := by
  intro w1 w2 heq
  have hinv : ∀ y, inverseSigmaFan x V E v (extensionSigmaFan x V E v y) = y := by
    intro y
    have h := (inverse_sigma_fan_comp hfan hu).1
    exact congrFun h y
  calc w1 = inverseSigmaFan x V E v (extensionSigmaFan x V E v w1) := (hinv w1).symm
    _ = inverseSigmaFan x V E v (extensionSigmaFan x V E v w2) := by rw [heq]
    _ = w2 := hinv w2

end Kepler.Text.Fan

/- 计划（F3）：azim 基础引理层（flyspeck.ml 的 AZIM_REFL/AZIM_SYMM 等）→
fan.hl 的 sigma_fan_in_set_of_edge/permutes_sigma_fan/INVERSE1_SIGMA_FAN →
fan_misc 剩余三引理；随后 hypermapOfFan（证明参数化）与
conforming_bijection（需 Hypermap.faceSet）。 -/
